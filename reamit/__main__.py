import sys
from builtins import reversed

import ast
import astor
from argparse import ArgumentParser
from typing import List
from typing import Set


class Var:
    num_s_regs = 10
    num_t_regs = 10
    optimize = True

    def __init__(self, line, reg=None, num=None, name=None):
        self.reg = reg
        self.num = num
        self.name = name
        self.writes_to = []
        self.writes_from = []
        self.reads = []
        self.writes = [line]
        self.func_calls = []
        self.expired = False

    def write_to(self, dest: 'Var', line: int):
        self.writes_to.append((line, dest))

    def write_from(self, src: 'Var', line: int):
        self.writes_from.append((line, src))

    def mark_read(self, line: int):
        if line not in self.reads:
            self.reads.append(line)

    def mark_write(self, line: int):
        if line not in self.writes:
            self.writes.append(line)

    def mark_func_call(self, line: int):
        self.func_calls.append(line)

    @property
    def is_func_immune(self):
        if self.reg:
            return self.reg.startswith('s')
        if self.num is not None:
            return True
        return self.reads and self.func_calls and min(self.func_calls) < max(self.reads)

    def find_write_before(self, line):
        for i in reversed(self.writes):
            if i < line:
                return i
        return float('-inf')

    def find_read_after(self, line):
        for i in self.reads:
            if i > line:
                return i
        return float('inf')

    def merge_onto(self, other):
        other.reg = self.reg
        other.writes = self.writes = sorted(self.writes + other.writes)
        other.reads = self.reads = sorted(self.reads + other.reads)
        other.func_calls = self.func_calls = sorted(self.func_calls + other.func_calls)

    def quantize(self, used_regs: set, line_no: int):
        if self.num is not None:
            return
        if self.optimize and self.reg is None and len(self.writes_from) == 1:
            move_line, src = self.writes_from[0]
            born_from_move = self.writes[0] == move_line
            if born_from_move and not src.expired and src.reg is not None and len(self.writes) == 1 and (
                    not self.reads or src.find_write_before(max(self.reads)) <= move_line) and (
                    src.is_func_immune or not self.is_func_immune):
                src.merge_onto(self)

        if self.optimize and self.reg is None and len(self.writes_to) == 1:
            move_line, dest = self.writes_to[0]
            killed_from_move = max(self.reads) == move_line
            if killed_from_move and not dest.expired and dest.reg is not None and len(
                    self.reads) == 1 and dest.find_read_after(self.writes[0]) >= move_line and (
                    dest.is_func_immune or not self.is_func_immune):
                dest.merge_onto(self)

        if self.reg is None:
            if self.is_func_immune:
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

        if self.reads and line_no == max(self.reads):
            if self.reg in used_regs:
                used_regs.remove(self.reg)
                self.expired = True

    def __str__(self):
        if self.num is not None:
            return str(self.num)
        if self.reg is None:
            return '<Var {}>'.format(id(self) % 1000)
        else:
            return '$' + self.reg


class VarContext:
    def __init__(self, line_start):
        self.line_start = line_start
        self.vals = []  # type: List[Var]
        self.names = {}
        self.func_called = False

    def mark_func_call(self, line):
        self.func_called = True
        for val in self.vals:
            val.mark_func_call(line)

    def mark_func_called_between(self, start, end):
        for val in self.vals:
            if any(start <= i < end for i in val.reads) and end - 1 not in val.reads:
                val.reads.append(end - 1)
                val.reads.sort()
            if any(start <= i < end for i in val.writes) and end - 1 not in val.writes:
                val.writes.append(end - 1)
                val.writes.sort()

    def new(self, line, name='', reg=None, num=None):
        var = Var(line, reg, num, name=name)
        self.vals.append(var)
        if name:
            self.names[name] = var
        return var

    def __contains__(self, item):
        return item in self.names

    def __getitem__(self, item) -> Var:
        return self.names[item]


class AssemblerLine:
    pass


class Command(AssemblerLine):
    def __init__(self, inst, *args, imm=None, obj=None, fmt=None, reads=None, writes=None):
        self.imm = imm
        self.obj = obj
        self.inst = inst
        self.args = args
        self.fmt = fmt
        self.reads = reads or []
        self.writes = writes or []

    def get_comment(self):
        return '# ' + astor.to_source(self.obj).strip() if self.obj else ''

    @property
    def still_useful(self):
        if self.inst != 'move':
            return True
        dest, src = self.args
        return str(dest) != str(src)

    def __str__(self):
        inst = self.inst
        if self.imm:
            im_inst, var = self.imm
            if var.num is not None:
                inst = im_inst
        parts = [
            '',
            inst,
            (self.fmt.format(*self.args) if self.fmt else ', '.join(map(str, self.args)))
        ]
        if isinstance(self.obj, ast.AST):
            parts.append('# ' + astor.to_source(self.obj).strip())
        elif isinstance(self.obj, str):
            parts.append('# ' + self.obj)
        return '\t'.join(parts)


class Label(AssemblerLine):
    def __init__(self, label):
        self.label = label

    def __str__(self):
        return self.label + ':'


class Spacer(AssemblerLine):
    pass


class StackAlloc(AssemblerLine):
    pass


class StackDealloc(AssemblerLine):
    pass


class FuncGenerator:
    def __init__(self):
        self.lines = []
        self.stack = [VarContext(0)]
        self.new_var('__ra__', reg='ra')
        self.labels_stack = []

    @classmethod
    def generate(cls, source: str, filename: str = '<unknown>') -> list:
        mod = ast.parse(source, filename)
        assembly_lines = []
        for obj in mod.body:
            if not isinstance(obj, ast.FunctionDef):
                if isinstance(obj, ast.Assign) and isinstance(obj.value, ast.Ellipsis):
                    continue  # Ellipsis can be used to indicate externally resolved symbol
                raise cls._err(obj, 'Only functions can exist at the top level (line {1} col {2}).')

            if len(obj.body) == 1 and isinstance(obj.body[0], ast.Expr) and isinstance(obj.body[0].value, ast.Ellipsis):
                continue  # Empty function defs can be used to define externally resolved symbols

            gen = cls()
            gen.add(Spacer())
            gen.labels_stack.append((obj.name, obj))
            gen.add(Label(gen.cur_label))
            gen.add(StackAlloc())
            gen.add(Spacer())
            for i, arg in enumerate(obj.args.args):
                gen.assign(gen.new_var(arg.arg), gen.new_var(reg='a' + str(i)), obj=arg)
            gen.add(Spacer())
            for i in obj.body:
                gen.interpret(i)
            if obj.body and isinstance(obj.body[-1], ast.Return):
                gen.lines.pop()  # Remove last redundant jump
            gen.add(Label(gen.cur_label + '_end'))
            gen.add(StackDealloc())
            gen.inst('jr', gen.ctx['__ra__'])
            gen.labels_stack.pop()
            assembly_lines.extend(gen.quantize_lines())
        assembly_lines.append('')
        return assembly_lines

    def quantize_lines(self) -> list:
        used_regs = set()  # type: Set[str]
        all_used_regs = set()
        for line_no, line in enumerate(self.lines):
            if isinstance(line, Command):
                for var in line.reads:
                    var.quantize(used_regs, line_no)
                for var in line.writes:
                    var.quantize(used_regs, line_no)
                for var in line.reads + line.writes:
                    if var.reg:
                        all_used_regs.add(var.reg)
        s_regs = [i for i in all_used_regs if i.startswith('s')]
        saved_regs = ['ra'] * bool(self.ctx['__ra__'].func_calls) + s_regs

        lines = []
        last_line = None
        for line in self.lines:
            if isinstance(line, Command):
                if line.still_useful:
                    lines.append(str(line))
                    last_line = Command
            if isinstance(line, Label):
                lines.append('')
                lines.append(str(line))
                last_line = Label
            elif isinstance(line, Spacer):
                if last_line == Command:
                    lines.append('')
                    last_line = Spacer
            elif isinstance(line, StackAlloc):
                if saved_regs:
                    lines.append(str(Command('sub', '$sp', 4 * len(saved_regs), obj='Allocate stack')))
                    for i, reg in enumerate(sorted(saved_regs)):
                        lines.append(str(Command('sw', '$' + reg, i * 4, fmt='{}, {}($sp)')))
                    last_line = Command
            elif isinstance(line, StackDealloc):
                if saved_regs:
                    for i, reg in reversed(list(enumerate(sorted(saved_regs)))):
                        lines.append(str(Command('lw', '$' + reg, i * 4, fmt='{}, {}($sp)')))
                    lines.append(str(Command('add', '$sp', 4 * len(saved_regs), obj='Deallocate stack')))
                    last_line = Command
        return lines

    @property
    def cur_label(self):
        return '_'.join(name for name, obj in self.labels_stack)

    @property
    def ctx(self) -> VarContext:
        return self.stack[-1]

    @property
    def cur_line(self):
        return len(self.lines)

    @staticmethod
    def _err(obj, msg='Unsupported {} syntax at line {} col {}.') -> SyntaxError:
        return SyntaxError(msg.format(type(obj).__name__, obj.lineno, obj.col_offset))

    def new_var(self, name='', reg=None, num=None) -> Var:
        return self.ctx.new(self.cur_line, name, reg, num)

    def push_stack(self):
        self.stack.append(VarContext(self.cur_line))

    def pop_stack(self, has_loop=False):
        line_end = self.cur_line
        ctx = self.stack.pop()
        if has_loop:
            for i in self.stack:
                i.mark_func_called_between(ctx.line_start, line_end)

    def resolve(self, obj) -> Var:
        try:
            self.push_stack()
            if isinstance(obj, ast.Subscript):
                target = obj
                value = self.new_var()
                if not isinstance(target.slice, ast.Index):
                    raise self._err(target.slice)
                array = self.resolve(target.value)
                index = self.resolve(target.slice.value)
                if index.num is not None:
                    self.inst('lw', value, index, array, fmt='{}, {}({})', reads=[index, array], writes=[value],
                              obj=obj)
                else:
                    offset = self.new_var()
                    self.assign(offset, array, obj)
                    self.inst('add', offset, offset, index, reads=[offset, index], writes=[offset], obj=obj)
                    self.inst('lw', value, 0, offset, reads=[offset], writes=[value], fmt='{}, {}({})', obj=obj)
                return value
            if isinstance(obj, ast.Num):
                return self.new_var(num=obj.n)
            if isinstance(obj, ast.Call):
                for context in self.stack:
                    context.mark_func_call(self.cur_line)

                for i, arg in enumerate(obj.args):
                    self.assign(self.new_var(reg='a' + str(i)), self.resolve(arg), obj=arg)
                self.inst('jal', obj.func.id, obj=obj)
                return_var = self.new_var(reg='v0')
                out_var = self.new_var()
                self.assign(out_var, return_var, obj=obj)
                return out_var
            if isinstance(obj, ast.BinOp):
                left_val = self.resolve(obj.left)
                right_val = self.resolve(obj.right)
                op_to_inst = {
                    ast.Mult: 'mul',
                    ast.Add: 'add',
                    ast.Sub: 'sub'
                }
                if type(obj.op) not in op_to_inst:
                    raise self._err(obj.op, 'Unsupported operator {} at line {} col {}.')
                if isinstance(left_val, int):
                    raise self._err(obj.left, 'Numeric constant on left site unsupported (line {1} col {2})')

                var = self.new_var()
                inst = op_to_inst[type(obj.op)]
                self.inst(inst, var, left_val, right_val, reads=[left_val, right_val], writes=[var], obj=obj)
                return var
            if isinstance(obj, ast.Name):
                for ctx in reversed(self.stack):
                    if obj.id in ctx:
                        return ctx[obj.id]
                raise NameError("No such variable named '{}'.".format(obj.id))
            raise self._err(obj, 'Unsupported {} expression syntax at line {} col {}.')
        finally:
            self.pop_stack()

    def inst(self, inst, *args, reads=None, writes=None, obj=None, imm=None, fmt=None):
        if inst in ['sub', 'add'] and args[2].num == 0:
            self.assign(args[0], args[1], obj)
            return
        if inst == 'mul' and args[2].num == '1':
            self.assign(args[0], args[1], obj)
            return
        if inst == 'mul' and args[2].num == '0':
            self.assign(args[0], self.new_var(num=0))
            return

        for i in reads or []:
            i.mark_read(self.cur_line)
        for i in writes or []:
            i.mark_write(self.cur_line)
        self.lines.append(Command(inst, *args, imm=imm, obj=obj, fmt=fmt, reads=reads, writes=writes))

    def add(self, inst_line_obj):
        self.lines.append(inst_line_obj)

    def assign(self, dest, src, obj=None):
        dest.write_from(src, self.cur_line)
        src.write_to(dest, self.cur_line)
        self.inst('move', dest, src, reads=[src], writes=[dest], imm=('li', src), obj=obj)

    def assign_target(self, target: ast.AST, value: Var, obj=None):
        if isinstance(target, ast.Name):
            try:
                write_var = self.resolve(target)
            except NameError:
                write_var = self.new_var(target.id)
            self.assign(write_var, value, obj)
        elif isinstance(target, ast.Subscript):
            if not isinstance(target.slice, ast.Index):
                raise self._err(target.slice)
            array = self.resolve(target.value)
            index = self.resolve(target.slice.value)
            if index.num is not None:
                self.inst('sw', value, index, array, fmt='{}, {}({})', reads=[value, index, array], writes=[],
                          obj=obj)
            else:
                offset = self.new_var()
                self.assign(offset, array, obj)
                self.inst('add', offset, offset, index, reads=[offset, index], writes=[offset], obj=obj)
                self.inst('sw', value, 0, offset, reads=[value, offset], writes=[], fmt='{}, {}({})', obj=obj)
        else:
            raise self._err(target)

    def handle_assign(self, obj: ast.Assign):
        read_var = self.resolve(obj.value)
        for target in obj.targets:
            self.assign_target(target, read_var, obj)

    def handle_augassign(self, obj: ast.AugAssign):
        self.assign_target(obj.target, self.resolve(ast.BinOp(obj.target, obj.op, obj.value)))

    def handle_if(self, obj: ast.If):
        if len(obj.body) == 1:
            statm = obj.body[0]
            if isinstance(statm, ast.Continue):
                self.branch_compare(obj.test, self.cur_label)
                return
            elif isinstance(statm, ast.Return) and obj.body[0].value is None:
                self.branch_compare(obj.test, self.cur_label + '_end')
                return
        end_label = self.cur_label + '_skip_if'
        self.branch_compare(obj.test, end_label)
        for i in obj.body:
            self.interpret(i)
        self.add(Label(end_label))

    def branch_compare(self, obj: ast.Compare, jump_true_label):
        op = type(obj.ops[0])
        left_var = self.resolve(obj.left)
        right_var = self.resolve(obj.comparators[0])
        eq_op_to_inst = {
            ast.Eq: 'bne',
            ast.NotEq: 'beq'
        }
        cp_op_to_inst = {
            ast.Lt: 'bgez',
            ast.LtE: 'bgtz',
            ast.Gt: 'blez',
            ast.GtE: 'bltz'
        }
        if op in eq_op_to_inst:
            self.inst(eq_op_to_inst[op], left_var, right_var, jump_true_label, reads=[left_var, right_var], obj=obj)
        elif op in cp_op_to_inst:
            b_minus_a = self.resolve(ast.BinOp(obj.left, ast.Sub(), obj.comparators[0]))
            self.inst(cp_op_to_inst[op], b_minus_a, jump_true_label, reads=[b_minus_a], writes=[], obj=obj)
        else:
            raise self._err(obj.ops[0], 'Unsupported {} condition at line {} col {}.')

    def handle_while(self, obj: ast.While):
        if obj.orelse:
            raise self._err(obj.orelse)
        self.push_stack()
        self.labels_stack.append(('while', obj))
        label = self.cur_label
        end_label = label + '_end'
        self.add(Label(label))
        exp = obj.test
        if not isinstance(exp, ast.Compare) or len(exp.comparators) != 1:
            raise self._err(exp)

        self.branch_compare(exp, end_label)

        for i in obj.body:
            self.interpret(i)

        self.inst('j', label, reads=[], writes=[])
        self.add(Label(end_label))
        self.labels_stack.pop()
        self.pop_stack(True)

    @property
    def can_break(self):
        return self.labels_stack and isinstance(self.labels_stack[-1][1], ast.While)

    def handle_continue(self, obj: ast.Continue):
        if not self.can_break:
            raise self._err(obj, 'Continue not in loop (line {1} col {2}).')
        self.inst('j', self.cur_label, obj=obj)

    def handle_break(self, obj: ast.Break):
        if not self.can_break:
            raise self._err(obj, 'Break not in loop (line {1} col {2}).')
        self.inst('j', self.cur_label + '_end', obj=obj)

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
        if obj.value:
            expr_val = self.resolve(obj.value)
            return_var = self.new_var(reg='v0')
            self.assign(return_var, expr_val)
        self.inst('j', parent_func_label + '_end', obj=obj)

    def handle_expr(self, obj: ast.Expr):
        self.resolve(obj.value)

    def interpret(self, obj):
        typ = type(obj)
        if typ not in self.handlers:
            raise SyntaxError(
                'Unsupported {} syntax at line {} col {}.'.format(typ.__name__, obj.lineno, obj.col_offset))
        handler = self.handlers[typ]
        handler(self, obj)

    handlers = {
        ast.Assign: handle_assign,
        ast.AugAssign: handle_augassign,
        ast.While: handle_while,
        ast.Continue: handle_continue,
        ast.Break: handle_break,
        ast.Return: handle_return,
        ast.Expr: handle_expr,
        ast.If: handle_if
    }


def main():
    parser = ArgumentParser(description='Readable assembly code generator')
    parser.add_argument('input_files', nargs='*', help='Input .rm files. If not specified, from stdin')
    parser.add_argument('-o', '--output', help='Output MIPS .s file. If not specified, stdout')
    args = parser.parse_args()

    if not args.input_files and sys.stdin.isatty():
        parser.error('Please specify input files or pass input via stdin')

    lines = []

    for src in args.input_files:
        with open(src) as f:
            lines.extend(FuncGenerator.generate(f.read(), src))
    if not args.input_files:
        lines.extend(FuncGenerator.generate(sys.stdin.read(), '<stdin>'))

    if args.output:
        with open(args.output, 'w') as f:
            f.write('\n'.join(lines))
    else:
        print('\n'.join(lines))


if __name__ == '__main__':
    main()
