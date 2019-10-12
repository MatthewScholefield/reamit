import sys

import ast
from abc import abstractmethod, ABC
from argparse import ArgumentParser
from functools import partial
from typing import Any, Union
from typing import List
from typing import Set


class Var:
    num_s_regs = 10
    num_t_regs = 10
    optimize_move = True

    def __init__(self, name: str, start_line: int, init_reg: str = None):
        self.name = name
        self.start_line = start_line
        self.end_line = None  # type: int
        self.init_reg = init_reg
        self.func_call_between = False
        self.func_called = False
        self.reg = init_reg  # type: str
        self.move_dest = None  # type: Var
        self.move_src = None  # type: Union[Var, int]
        self.fixed = bool(init_reg)

    def mark_func_called(self):
        self.func_called = True

    def mark_access(self, line: int):
        if self.func_called:
            self.func_call_between = True
        self.end_line = line

    def mark_move_dest(self, dest: Union['Var', int]):
        self.move_dest = dest

    def mark_move_src(self, src: Union['Var', int]):
        self.move_src = src

    def quantize(self, used_regs: set, line_no: int):
        if self.reg is None:
            if self.optimize_move and self.move_dest is not None and \
                    self.move_dest.reg and \
                    self.move_dest.never_accessed:
                self.end_line = max(self.end_line or -1, self.move_dest.start_line)
                reg = self.move_dest.reg
                self.fixed = True
            elif self.func_call_between:
                for i in range(self.num_s_regs):
                    reg = 's' + str(i)
                    if reg not in used_regs:
                        break
                else:
                    raise RuntimeError('No more s registers available.')
            else:
                for i in range(self.num_t_regs):
                    reg = 't' + str(i)
                    if reg not in used_regs:
                        break
                else:
                    raise RuntimeError('No more t registers available')
            used_regs.add(reg)
            self.reg = reg
        if self.optimize_move and self.never_accessed:
            if self.move_dest is not None and not self.move_dest.func_call_between and not self.move_dest.fixed:
                self.move_dest.reg = self.reg
                self.move_dest.fixed = True
                self.fixed = True
                used_regs.add(self.reg)
        if line_no == self.end_line:
            if self.reg in used_regs:
                used_regs.remove(self.reg)

    @property
    def never_accessed(self):
        return self.end_line is None

    def __str__(self):
        if self.reg is None:
            return '<Var {}>'.format(id(self))
        else:
            return '$' + self.reg


class Inst(ABC):
    @abstractmethod
    def __str__(self):
        pass

    @property
    @abstractmethod
    def vars(self) -> list:
        pass


class AssignInst(Inst):
    def __init__(self, dest, src):

        if isinstance(dest, Var):
            dest.mark_move_src(src)
        if isinstance(src, Var):
            src.mark_move_dest(dest)
        self.dest = dest
        self.src = src

    def __str__(self):
        dest_str = str(self.dest)
        src_str = str(self.src)
        if dest_str == src_str:
            return ''
        return '{} {}, {}'.format('move' if isinstance(self.src, Var) else 'li', dest_str, src_str)

    @property
    def vars(self):
        return [self.dest, self.src]


class MathInst(Inst):
    def __init__(self, inst, im_inst, dest, src1, src2):
        self.inst = inst
        self.im_inst = im_inst
        self.dest = dest
        self.src1 = src1
        self.src2 = src2

    def __str__(self):
        return '{} {}, {}, {}'.format(
            self.inst if isinstance(self.src2, Var) else self.im_inst, self.dest, self.src1, self.src2
        )

    @property
    def vars(self):
        return [self.dest, self.src1, self.src2]


class BranchInst(Inst):
    def __init__(self, inst, num, *args):
        assert len(args) == num
        if num == 2:
            self.a, self.label = args
            self.b = None
        else:
            self.a, self.b, self.label = args
        self.inst = inst

    def __str__(self):
        s = '{} {}'.format(self.inst, self.a)
        if self.b is not None:
            s += ', {}'.format(self.b)
        s += ', {}'.format(self.label)
        return s

    @property
    def vars(self):
        return [self.a, self.label] if self.b is None else [self.a, self.b, self.label]


def make_math_inst(inst, inst_im, ignore_val=None):
    def math_inst(dest, src1, src2, inst=inst, inst_im=inst_im, ignore_val=ignore_val):
        if src2 != ignore_val:
            return MathInst(inst, inst_im, dest, src1, src2)
        else:
            return AssignInst(dest, src1)

    return math_inst


inst_assign = AssignInst

inst_add = make_math_inst('add', 'addi', 0)
inst_sub = make_math_inst('sub', 'sub', 0)
inst_mul = make_math_inst('mul', 'mul')
inst_and = make_math_inst('and', 'andi')
inst_or = make_math_inst('or', 'ori')
inst_xor = make_math_inst('xor', 'xori')

inst_beq = partial(BranchInst, 'beq', 3)
inst_bne = partial(BranchInst, 'bne', 3)
inst_bltz = partial(BranchInst, 'bltz', 2)
inst_blez = partial(BranchInst, 'blez', 2)
inst_bgtz = partial(BranchInst, 'bgtz', 2)
inst_bgez = partial(BranchInst, 'bgez', 2)


class AssemblyGenerator:
    op_to_inst = {
        ast.Mult: inst_mul,
        ast.Add: inst_add,
        ast.Sub: inst_sub
    }

    def __init__(self):
        self.lines = []
        self.in_scope_vars = []  # type: List[Var]
        self.name_to_var = {}
        self.labels_stack = []
        self.called_func = False

    @classmethod
    def generate(cls, source: str, filename: str = '<unknown>') -> list:
        mod = ast.parse(source, filename)
        assembly_lines = []
        for obj in mod.body:
            if not isinstance(obj, ast.FunctionDef):
                raise cls._err(obj, 'Only functions can exist at the top level (line {1} col {2}).')

            gen = cls()
            for i, arg in enumerate(obj.args.args):
                gen.lines.append(
                    (inst_assign(gen.reg(Var(arg.arg, gen.cur_line)), Var('', gen.cur_line, 'a' + str(i))), arg))

            gen.lines.append(' ')  # Add a newline
            gen.labels_stack.append((obj.name, obj))
            start_label = '{}:'.format(gen.cur_label)
            for i in obj.body:
                gen.interpret(i)
            if obj.body and isinstance(obj.body[-1], ast.Return):
                gen.lines.pop()  # Remove last redundant jump
            gen.lines.append('{}_end:'.format(gen.cur_label))
            gen.labels_stack.pop()
            assembly_lines.append('')
            assembly_lines.append(start_label)
            assembly_lines.extend(gen.quantize_lines(source.split('\n')))
        assembly_lines.append('')
        return assembly_lines

    def quantize_lines(self, source_lines: list) -> list:
        used_regs = set()  # type: Set[str]
        all_used_regs = set()
        middle_lines = []
        for line_no, line in enumerate(self.lines):
            if isinstance(line, tuple):
                line, comment = line
            else:
                line, comment = line, None
            if hasattr(comment, 'lineno'):
                comment = source_lines[comment.lineno - 1][comment.col_offset:]
                end_col = len(comment)
                try:
                    ast.parse(comment, 'eval')
                except SyntaxError as e:
                    end_col = e.offset - 1
                comment = comment[:end_col]

            if isinstance(line, Inst):
                for var in reversed(line.vars):
                    if isinstance(var, Var):
                        var.quantize(used_regs, line_no)
                        all_used_regs.add(var.reg)
            if line:
                middle_lines.append((str(line), comment))
        s_regs = [i for i in all_used_regs if i.startswith('s')]
        saved_regs = s_regs
        if self.called_func:
            saved_regs.insert(0, 'ra')
        start_lines = []
        end_lines = []
        if saved_regs:
            start_lines.append(('sub $sp, {}'.format(4 * len(saved_regs)), 'Allocate stack'))
            for i, reg in enumerate(saved_regs):
                start_lines.append(('sw ${}, {}($sp)'.format(reg, i * 4), ''))
            for i, reg in reversed(list(enumerate(saved_regs))):
                end_lines.append(('lw ${}, {}($sp)'.format(reg, i * 4), ''))
            end_lines.append(('add $sp, {}'.format(4 * len(saved_regs)), 'Deallocate stack'))

        end_lines.append(('jr $ra', ''))
        lines = []

        if self.called_func and middle_lines and not middle_lines[0][0].isspace():
            start_lines.append((' ', ''))
            start_lines.append((' ', '=== Arguments ==='))

        for line, comment in start_lines + middle_lines + end_lines:
            if not line:
                continue
            if line.isspace():
                if comment:
                    lines.append('\t# ' + comment)
                else:
                    lines.append('')
                continue
            if line.endswith(':'):
                line = '\n' + line
            else:
                command, *others = line.split(' ')
                line = '\t{}\t{}'.format(command, ' '.join(others))
                if comment:
                    line += '\t# ' + comment
            lines.append(line)
        return lines

    def interpret(self, obj):
        typ = type(obj)
        if typ not in self.handlers:
            raise SyntaxError(
                'Unsupported {} syntax at line {} col {}.'.format(typ.__name__, obj.lineno, obj.col_offset))
        handler = self.handlers[typ]
        handler(self, obj)

    def resolve_to_val(self, obj: Any) -> Union[Var, int]:
        if isinstance(obj, int):
            return obj
        if isinstance(obj, Var):
            return obj
        if isinstance(obj, ast.Expr):
            return self.resolve_to_val(obj.value)
        if isinstance(obj, ast.Num):
            return obj.n
        if isinstance(obj, ast.Call):
            self.called_func = True
            for i in self.in_scope_vars:
                i.mark_func_called()
            for i, arg in enumerate(obj.args):
                self.lines.append((inst_assign(Var('', self.cur_line, 'a' + str(i)), self.resolve_to_val(arg)), arg))

            self.lines.append(('jal {}'.format(obj.func.id), obj))

            var = self.reg(Var('', self.cur_line, 'v0'))
            self._mark_access(var)
            out_var = self.reg(Var('', self.cur_line))
            self.lines.append((inst_assign(out_var, var), obj))
            return out_var
        if isinstance(obj, ast.BinOp):
            left_val = self.resolve_to_val(obj.left)
            right_val = self.resolve_to_val(obj.right)
            if type(obj.op) not in self.op_to_inst:
                raise self._err(obj.op, 'Unsupported operator at line {} col {}.')
            inst = self.op_to_inst[type(obj.op)]

            var = self.reg(Var('', self.cur_line))
            self._mark_access(left_val)
            self._mark_access(right_val)
            self.lines.append((inst(var, left_val, right_val), obj))
            return var
        if isinstance(obj, ast.Name):
            if obj.id not in self.name_to_var:
                raise NameError("No such variable named '{}'.".format(obj.id))
            var = self.name_to_var[obj.id]  # type: Var
            self._mark_access(var)
            return var
        raise self._err(obj, 'Unsupported {} expression syntax at line {} col {}.')

    def _mark_access(self, val: Union[Var, int]):
        if isinstance(val, Var):
            val.mark_access(self.cur_line)

    @staticmethod
    def _err(obj, msg='Unsupported {} syntax at line {} col {}.') -> SyntaxError:
        return SyntaxError(msg.format(type(obj).__name__, obj.lineno, obj.col_offset))

    @property
    def cur_line(self):
        return len(self.lines)

    def reg(self, var):
        self.in_scope_vars.append(var)
        self.name_to_var[var.name] = var
        return var

    @property
    def cur_label(self):
        return '_'.join(name for name, obj in self.labels_stack)

    def handle_assign(self, obj: ast.Assign):
        value = self.resolve_to_val(obj.value)
        for target in obj.targets:
            if target.id in self.name_to_var:
                var = self.name_to_var[target.id]
                if var.func_called and not var.func_call_between:
                    self.in_scope_vars.remove(var)
                    del self.name_to_var[var.name]
                    var = self.reg(Var(var.name, self.cur_line))
            else:
                var = self.reg(Var(target.id, self.cur_line))
            self.lines.append((inst_assign(var, value), obj))

    def handle_augassign(self, obj: ast.AugAssign):
        value = self.resolve_to_val(obj.value)
        target = obj.target
        if target.id in self.name_to_var:
            var = self.name_to_var[target.id]
            if var.func_called and not var.func_call_between:
                self.in_scope_vars.remove(var)
                del self.name_to_var[var.name]
                var = self.reg(Var(var.name, self.cur_line))
        else:
            var = self.reg(Var(target.id, self.cur_line))
        bin_op = ast.BinOp(target, obj.op, value)
        bin_op.lineno = obj.lineno
        bin_op.col_offset = obj.col_offset
        if type(obj.op) not in self.op_to_inst:
            raise self._err(obj.op, 'Unsupported operator at line {} col {}.')
        self.lines.append((self.op_to_inst[type(obj.op)](var, var, value), obj))

    def handle_if(self, obj: ast.If):
        if len(obj.body) == 1:
            if isinstance(obj.body[0], ast.Continue):
                self.branch_compare(obj.test, self.cur_label)
                return
            elif isinstance(obj.body[0], ast.Return) and obj.body[0].value is None:
                self.branch_compare(obj.test, self.cur_label + '_end')
                return
        end_label = self.cur_label + '_skip_if'
        self.branch_compare(obj.test, end_label)
        for i in obj.body:
            self.interpret(i)
        self.lines.append(end_label + ':')

    def branch_compare(self, obj: ast.Compare, jump_true_label):
        op = type(obj.ops[0])
        left_var = self.resolve_to_val(obj.left)
        right_var = self.resolve_to_val(obj.comparators[0])
        if op == ast.Eq:
            self.lines.append((inst_bne(left_var, right_var, jump_true_label), obj))
        elif op == ast.NotEq:
            self.lines.append((inst_beq(left_var, right_var, jump_true_label), obj))
        else:
            op_to_inst = {
                ast.Lt: inst_bgez,
                ast.LtE: inst_bgtz,
                ast.Gt: inst_blez,
                ast.GtE: inst_bltz
            }
            if op not in op_to_inst:
                raise self._err(obj.ops[0], 'Unsupported {} condition at line {} col {}.')
            bin_op = ast.BinOp(left_var, ast.Sub(), right_var)
            bin_op.lineno = obj.lineno
            bin_op.col_offset = obj.col_offset
            b_minus_a = self.resolve_to_val(bin_op)
            self.lines.append((op_to_inst[op](b_minus_a, jump_true_label), obj))

    def handle_while(self, obj: ast.While):
        if obj.orelse:
            raise self._err(obj.orelse)
        self.labels_stack.append(('while', obj))
        label = self.cur_label
        end_label = label + '_end'
        self.lines.append(label + ':')
        exp = obj.test
        if not isinstance(exp, ast.Compare) or len(exp.comparators) != 1:
            raise self._err(exp)

        self.branch_compare(obj.test, end_label)

        for i in obj.body:
            self.interpret(i)

        self.lines.append(end_label + ':')
        self.labels_stack.pop()

    @property
    def can_break(self):
        return self.labels_stack and isinstance(self.labels_stack[-1][1], ast.While)

    def handle_continue(self, obj: ast.Continue):
        if not self.can_break:
            raise self._err(obj, 'Continue not in loop (line {1} col {2}).')
        self.lines.append(('j {}'.format(self.cur_label), obj))

    def handle_break(self, obj: ast.Break):
        if not self.can_break:
            raise self._err(obj, 'Break not in loop (line {1} col {2}).')
        self.lines.append(('j {}'.format(self.cur_label + '_end'), obj))

    @property
    def parent_func_label(self):
        for i, (name, obj) in reversed(list(enumerate(self.labels_stack))):
            if isinstance(obj, ast.FunctionDef):
                return '_'.join(name for name, obj in self.labels_stack[:i + 1])
        return None

    def handle_return(self, obj: ast.Return):
        parent_func_label = self.parent_func_label
        if not parent_func_label:
            raise self._err(obj, 'Return not within function (line {1} col {2}).')
        return_val = obj.value
        if return_val:
            return_var = self.reg(Var('', self.cur_line, 'v0'))
            self.lines.append((inst_assign(return_var, self.resolve_to_val(return_val)), obj))
        self.lines.append(('j {}'.format(parent_func_label + '_end'), obj))

    def handle_expr(self, obj: ast.Expr):
        val = obj.value
        if isinstance(val, ast.Call):
            self.called_func = True
            for i in self.in_scope_vars:
                i.mark_func_called()
            for i, arg in enumerate(val.args):
                self.lines.append((inst_assign(Var('', self.cur_line, 'a' + str(i)), self.resolve_to_val(arg)), arg))
            self.lines.append(('jal {}'.format(val.func.id), val))
        else:
            print('Warning: Unused expression (line {} col {}).'.format(obj.lineno, obj.col_offset), file=sys.stderr)
            self.resolve_to_val(val)

    handlers = {
        ast.Assign: handle_assign,
        ast.While: handle_while,
        ast.Continue: handle_continue,
        ast.Break: handle_break,
        ast.Return: handle_return,
        ast.Expr: handle_expr,
        ast.AugAssign: handle_augassign,
        ast.If: handle_if
    }


def main():
    parser = ArgumentParser(description='Readable assembly code generator')
    parser.add_argument('input_files', nargs='*', help='Input .rm files. If not specified, from stdin')
    parser.add_argument('-o', '--output', help='Output MIPS .s file. If not specified, stdout')
    args = parser.parse_args()

    if not args.input_files and sys.stdin.isatty():
        parser.error('Please sepcify input files or pass input via stdin')

    lines = []

    for src in args.input_files:
        with open(src) as f:
            lines.extend(AssemblyGenerator.generate(f.read(), src))
    if not args.input_files:
        lines.extend(AssemblyGenerator.generate(sys.stdin.read(), '<stdin>'))

    if args.output:
        with open(args.output, 'w') as f:
            f.write('\n'.join(lines))
    else:
        print('\n'.join(lines))


if __name__ == '__main__':
    main()
