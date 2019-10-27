import sys
from builtins import reversed

import ast
import astor
from argparse import ArgumentParser
from enum import Enum
from typing import List
from typing import Set


class Types(Enum):
    INTS = 1
    BYTES = 2
    INT = 3


class Var:
    num_s_regs = 8
    num_t_regs = 8
    optimize_level = 1

    def __init__(self, line, reg=None, num=None, name=None, typ=None):
        self.reg = reg
        self.num = num
        self.name = name
        self.writes_to = []
        self.writes_from = []
        self.reads = []
        self.writes = [line]
        self.func_calls = []
        self.expired = False
        self.typ = typ  # Type info
        self.linked = None

    @property
    def lnk(self):
        ref = self
        while ref.linked:
            ref = ref.linked
        return ref

    def get_byte_offset(self):
        if not self.typ:
            raise TypeError()
        if self.typ == Types.INTS:
            return 4
        if self.typ == Types.BYTES:
            return 1

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
        other.linked = self
        elem_to_self_writes_to = {elem: (line, elem) for line, elem in self.writes_to}

        if other in elem_to_self_writes_to:
            line, _ = elem_to_self_writes_to[other]
            self.writes_to.remove((line, other))
            other.writes_from.remove((line, self))
            self.reads.remove(line)
            other.writes.remove(line)

        other.writes = self.writes = sorted(self.writes + other.writes)
        other.reads = self.reads = sorted(self.reads + other.reads)
        other.func_calls = self.func_calls = sorted(self.func_calls + other.func_calls)

    def get_candidate(self, used_regs):
        if self.is_func_immune:
            for i in range(self.num_s_regs):
                reg = 's' + str(i)
                if reg not in used_regs:
                    return reg
            else:
                raise RuntimeError('No more s registers available.')
        else:
            for i in range(self.num_t_regs):
                reg = 't' + str(i)
                if reg not in used_regs:
                    return reg
            else:
                raise RuntimeError('No more t registers available')

    def quantize(self, used_regs: set, line_no: int):
        if self.num is not None:
            return
        if self.linked:
            return
        if self.optimize_level >= 1 and self.reg is None and (
                ((len(self.writes_from) == 1) and (self.optimize_level == 1)) or
                ((len(self.writes_from) >= 1) and (self.optimize_level > 1))
        ):
            move_line, src = self.writes_from[0]
            born_from_move = self.writes[0] == move_line
            if (
                    born_from_move and
                    not src.expired and
                    src.lnk.reg is not None and
                    (
                            len(self.writes_from) == 1 or
                            len(src.reads) == 1
                    ) and
                    (
                            not self.reads or
                            src.find_write_before(max(self.reads)) <= move_line
                    ) and
                    (
                            src.is_func_immune or
                            not self.is_func_immune
                    )
            ):
                src.merge_onto(self)
                return

        if self.optimize_level >= 1 and self.reg is None and len(self.writes_to) == 1:
            move_line, dest = self.writes_to[0]
            killed_from_move = max(self.reads) == move_line
            if (
                    killed_from_move and
                    not dest.expired and
                    (
                            (self.optimize_level == 1 and dest.lnk.reg is not None) or
                            self.optimize_level > 1
                    ) and
                    dest.find_read_after(self.writes[0]) >= move_line and
                    (
                            dest.is_func_immune or
                            not self.is_func_immune
                    )
            ):
                dest.merge_onto(self)
                return

        if self.reg is None:
            reg = self.get_candidate(used_regs)
            used_regs.add(reg)
            self.reg = reg

        if self.reads and line_no == max(self.reads):
            if self.reg in used_regs:
                used_regs.remove(self.reg)
                self.expired = True

    def __str__(self):
        if self.num is not None:
            return str(self.num)
        if self.linked:
            return str(self.linked)
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

    def new(self, line, name='', reg=None, num=None, typ=None):
        var = Var(line, reg, num, name=name, typ=typ)
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

    def get_comment(self) -> str:
        if isinstance(self.obj, ast.AST):
            return astor.to_source(self.obj).strip().split('\n')[0]
        elif isinstance(self.obj, str):
            return self.obj
        else:
            return ''

    def is_linked_to(self, other: 'Command') -> bool:
        return (
                (len(other.writes) == 1 and other.writes[0] in self.reads) or
                (len(self.writes) == 1 and self.writes[0] in other.reads)
        )

    @property
    def still_useful(self):
        if self.inst == 'nop':
            return False
        if self.inst != 'move':
            return True
        dest, src = self.args
        return str(dest) != str(src)

    def extra_commands(self):
        extra_commands = []
        mapping = {}
        for var in self.reads:
            if var.lnk.num == 0 and (not self.imm or var.lnk is not self.imm[1].lnk):
                mapping[var] = Var(var.writes[0], reg='0')
            elif var.lnk.num is not None and (not self.imm or var.lnk is not self.imm[1].lnk):
                r = Var(var.writes[0])
                mapping[var] = r
                extra_commands += [Command('li', r, var, writes=[r], reads=[var])]
        self.args = [mapping.get(arg, arg) for arg in self.args]
        return extra_commands

    def absorb_line(self, line: 'Command'):
        """Takes comment from another line if useful"""
        if self.is_linked_to(line) or line.inst == 'nop':
            self.obj = line.obj
            return True
        return False

    def __str__(self):
        inst = self.inst
        if self.imm:
            im_inst, var = self.imm
            if var.num is not None:
                inst = im_inst
        comment = self.get_comment()
        parts = [
            '',
            inst,
            (self.fmt.format(*self.args) if self.fmt else ', '.join(map(str, self.args)))
        ] + ['# ' + comment] * bool(comment)
        return '\t'.join(parts)


class Label(AssemblerLine):
    def __init__(self, label):
        self.label = label

    def __str__(self):
        return self.label + ':'


class Spacer(AssemblerLine):
    pass


class GlobalDef(AssemblerLine):
    def __init__(self, label):
        self.label = label

    def __str__(self):
        return '.globl ' + self.label


class StackAlloc(AssemblerLine):
    pass


class StackDealloc(AssemblerLine):
    pass


class StrDef(AssemblerLine):
    def __init__(self, name, string):
        self.name = name
        self.string = string

    def __str__(self):
        return '{}: .asciiz "{}"'.format(self.name,
                                         self.string.replace('\n', r'\n').replace('\t', r'\t').replace('"', r'\"'))


class NumDef(AssemblerLine):
    def __init__(self, name, num):
        self.name = name
        self.num = num

    def __str__(self):
        return '{} = {}'.format(self.name, self.num)


class FuncGenerator:
    def __init__(self, constants):
        self.constants = constants
        self.lines = []
        self.stack = [VarContext(0)]
        self.new_var('__ra__', reg='ra')
        self.labels_stack = []
        self.used_labels = set()
        for name, val in constants.items():
            self.new_var(name, num=name)

        self.custom_commands = {
            'mtc0': self.custom_mtc0,
            'mfc0': self.custom_mfc0,
            'r': self.custom_r
        }

    def custom_mfc0(self, cp_reg):
        var = self.new_var('')
        self.inst('mfc0', var, cp_reg, reads=[cp_reg], writes=[var])
        return var

    def custom_mtc0(self, src, cp_reg):
        self.inst('mtc0', src, cp_reg, reads=[src, cp_reg], writes=[])
        return None

    def custom_r(self, a):
        if not isinstance(a.num, int):
            raise TypeError('r must be passed a register number')
        return self.new_var(reg=str(a.num))

    def disambiguate_label(self, identifier, suffix=None):
        self.labels_stack.append((identifier, None))
        n = 1
        while self.cur_label in self.used_labels or (suffix and self.cur_label + suffix in self.used_labels):
            self.labels_stack.pop()
            n += 1
            self.labels_stack.append((identifier + '_' + str(n), None))
        self.used_labels.add(self.cur_label)
        if suffix:
            self.used_labels.add(self.cur_label + suffix)
        resolved_id = self.labels_stack[-1][0]
        self.labels_stack.pop()
        return resolved_id

    def get_label(self, identifier):
        return self.cur_label + self.disambiguate_label(identifier)

    def push_label(self, obj, identifier, suffix):
        self.labels_stack.append((self.disambiguate_label(identifier, suffix), obj))

    def pop_label(self):
        self.labels_stack.pop()

    @classmethod
    def generate(cls, source: str, filename: str = '<unknown>', debug=False) -> list:
        mod = ast.parse(source, filename)
        assembly_lines = []
        constants = {}
        for obj in mod.body:
            if not isinstance(obj, ast.FunctionDef):
                if isinstance(obj, ast.Assign):
                    for target in obj.targets:
                        assert isinstance(target, ast.Name)
                        if isinstance(obj.value, ast.Ellipsis):
                            constants[target.id] = None
                        if isinstance(obj.value, ast.Str):
                            constants[target.id] = obj.value.s
                            assembly_lines.append(str(StrDef(target.id, obj.value.s)))
                        if isinstance(obj.value, ast.Num):
                            constants[target.id] = obj.value.n
                            assembly_lines.append(str(NumDef(target.id, obj.value.n)))
                    continue
                if isinstance(obj, ast.Expr) and isinstance(obj.value, ast.Str):
                    assembly_lines.extend(obj.value.s.strip().split('\n'))
                    continue
                raise cls._err(obj, 'Only functions can exist at the top level (line {1} col {2}).')

            constants[obj.name] = None

            if len(obj.body) == 1 and isinstance(obj.body[0], ast.Expr) and isinstance(obj.body[0].value, ast.Ellipsis):
                continue  # Empty function defs can be used to define externally resolved symbols
            gen = cls(constants)
            gen.add(Spacer())
            gen.add(GlobalDef(obj.name))
            gen.push_label(obj, obj.name, '_end')
            gen.add(Label(gen.cur_label))
            gen.add(StackAlloc())
            gen.add(Spacer())
            for i, arg in enumerate(obj.args.args):
                t = arg.annotation
                typ = None
                if isinstance(t, ast.Name):
                    label = t.id
                    name_to_typ = {'ints': Types.INTS, 'bytes': Types.BYTES, 'int': Types.INT, 'bool': Types.INT}
                    if label not in name_to_typ:
                        raise gen._err(arg, 'No such {} type (line {{1}} col {{2}}).'.format(label))
                    typ = name_to_typ[label]
                gen.assign(gen.new_var(arg.arg, typ=typ), gen.new_var(reg='a' + str(i)), obj=arg)
            gen.add(Spacer())
            for i in obj.body:
                gen.interpret(i)
            if obj.body and isinstance(obj.body[-1], ast.Return):
                gen.lines.pop()  # Remove last redundant jump
            gen.add(Label(gen.cur_label + '_end'))
            gen.add(StackDealloc())
            gen.inst('jr', gen.ctx['__ra__'])
            gen.pop_label()
            if assembly_lines:
                assembly_lines.append('')
            assembly_lines.extend(gen.quantize_lines(debug))
        assembly_lines.append('')
        return assembly_lines

    def quantize_lines(self, debug=False) -> list:
        used_regs = set()  # type: Set[str]
        all_used_regs = set()
        mod_lines = []
        for line_no, line in enumerate(self.lines):
            if isinstance(line, Command):
                for var in line.reads:
                    var.quantize(used_regs, line_no)
                for var in line.writes:
                    var.quantize(used_regs, line_no)
                for var in line.reads + line.writes:
                    if var.reg:
                        all_used_regs.add(var.reg)
                for new_cmd in line.extra_commands():
                    for var in new_cmd.reads:
                        var.quantize(used_regs, line_no)
                    for var in new_cmd.writes:
                        var.quantize(used_regs, line_no)
                    mod_lines.append(new_cmd)
            mod_lines.append(line)
        self.lines = mod_lines

        if debug:
            print('=== Raw Commands ===', file=sys.stderr)
            print('\n'.join('{}: {}'.format(i, line) for i, line in enumerate(self.lines)), file=sys.stderr)
            print(file=sys.stderr)

        s_regs = [i for i in all_used_regs if i.startswith('s')]
        saved_regs = ['ra'] * bool(self.ctx['__ra__'].func_calls) + s_regs

        lines = []
        last_line = None
        for i, line in enumerate(self.lines):
            if isinstance(line, Command):
                if line.still_useful:
                    lines.append(str(line))
                    last_line = Command
                elif line.obj:
                    if isinstance(self.lines[i - 1], Command) and self.lines[i - 1].absorb_line(line):
                        lines[-1] = str(self.lines[i - 1])
                        self.lines[i] = None
            elif isinstance(line, Label):
                if last_line != GlobalDef:
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
                    lines.append(str(Command('addi', '$sp', 4 * len(saved_regs), obj='Deallocate stack')))
                    last_line = Command
            elif isinstance(line, AssemblerLine):
                lines.append(str(line))
                last_line = type(line)
            else:
                raise RuntimeError('Unknown type in lines')
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
        return SyntaxError(msg.format(type(obj).__name__, getattr(obj, 'lineno', '?'), getattr(obj, 'col_offset', '?')))

    def new_var(self, name='', reg=None, num=None, typ=None) -> Var:
        return self.ctx.new(self.cur_line, name, reg, num, typ=typ)

    def push_stack(self):
        self.stack.append(VarContext(self.cur_line))

    def pop_stack(self, has_loop=False):
        line_end = self.cur_line
        ctx = self.stack.pop()
        if has_loop:
            for i in self.stack:
                i.mark_func_called_between(ctx.line_start, line_end)

    def find_var(self, name):
        for ctx in reversed(self.stack):
            if name in ctx:
                return ctx[name]
        raise NameError("No such variable named '{}'.".format(name))

    def resolve(self, obj) -> Var:
        try:
            self.push_stack()
            if isinstance(obj, ast.Subscript):
                target = obj
                value = self.new_var()
                array = self.resolve(target.value)

                if not isinstance(target.slice, ast.Index):
                    raise self._err(target.slice)
                if isinstance(target.slice.value, ast.Tuple):
                    index = None
                else:
                    index = self.resolve(target.slice.value)
                try:
                    offs = array.get_byte_offset()
                except TypeError as e:
                    print('No type defined for {} variable (line {} col {}).'.format(target.value, obj.lineno,
                                                                                     obj.col_offset),
                          file=sys.stderr)  # TODO: Make error
                    array.typ = Types.INTS
                    offs = 1

                typ = array.typ
                inst = {Types.INTS: 'lw', Types.BYTES: 'lb'}[typ]
                if index and index.num is not None:
                    self.inst(inst, value, self.new_var(num=offs * index.num), array, fmt='{}, {}({})',
                              reads=[index, array], writes=[value],
                              obj=obj)
                else:
                    offset = self.new_var()
                    if index is not None:
                        self.assign(offset, index, obj)
                        byte_mul = self.new_var(num=offs)
                        self.inst('mul', offset, offset, byte_mul, reads=[byte_mul, offset], writes=[offset], imm=('mul', byte_mul))
                        self.inst('add', offset, offset, array, reads=[offset, array], writes=[offset], obj=obj, imm=('addi', array))
                        memloc = offset
                    else:
                        memloc = array
                    self.inst(inst, value, 0, memloc, reads=[memloc], writes=[value], fmt='{}, {}({})', obj=obj)
                return value
            if isinstance(obj, ast.Str):
                if len(obj.s) != 1:
                    raise self._err(obj, 'Strings are not supported. Only char constants are allowed (line {} col {})')
                return self.new_var(num=ord(obj.s))
            if isinstance(obj, ast.NameConstant):
                if not obj in [True, False, None]:
                    raise self._err(obj, 'Unsupported constant {} (line {} col {}).')
                return self.new_var(num=1 if obj.value else 0)
            if isinstance(obj, ast.BoolOp):
                op = type(obj.op)
                if not all(type(i) in [ast.Compare, ast.NameConstant] for i in obj.values):
                    raise self._err(obj, 'Unsupported {} expression in boolean expression (line {} col {}).')
                exp = obj.values[0]
                for value in obj.values[1:]:
                    exp = ast.BinOp(exp, {ast.Or: ast.BitOr, ast.And: ast.BitAnd}[op](), value)
                return self.resolve(exp)
            if isinstance(obj, ast.Compare):
                left = self.resolve(obj.left)
                right = self.resolve(obj.comparators[0])
                if left.num is not None and right.num is not None:
                    exp = ast.Expression(ast.BinOp(ast.Num(self.constants.get(left.num, left.num)), obj.op,
                                                   ast.Num(self.constants.get(right.num, right.num))))
                    return self.new_var(num=eval(compile(exp, '', mode='eval')))

                op = type(obj.ops[0])
                invert_output = False
                if left.num is not None:
                    left, right = right, left
                    op = {ast.Lt: ast.Gt, ast.LtE: ast.GtE, ast.Eq: ast.Eq, ast.NotEq: ast.NotEq}[op]

                if right.num is not None:
                    if op == ast.GtE:
                        invert_output = True
                        op = ast.Lt
                    if op == ast.Gt:
                        invert_output = True
                        op = ast.LtE
                    if op == ast.LtE:
                        right = self.new_var(num=right.num + 1)
                        op = ast.Lt

                if op == ast.Gt:
                    inst = 'sgt'
                elif op == ast.GtE:
                    inst = 'sge'
                elif op == ast.Lt:
                    inst = 'slt' if right.num is None else 'slti'
                elif op == ast.LtE:
                    inst = 'sle'
                elif op == ast.Eq:
                    inst = 'seq'
                    if right.num is not None:
                        new_right = self.new_var()
                        self.assign(new_right, right, obj=obj)
                elif op == ast.NotEq:
                    inst = 'sne'
                else:
                    raise self._err(obj)

                out = self.new_var()
                self.inst(inst, out, left, right, reads=[left, right], writes=[out], obj=obj)
                if invert_output:
                    self.inst('xori', out, out, 1, reads=[out], writes=[out], obj=obj)
                return out
            if isinstance(obj, ast.Num):
                return self.new_var(num=obj.n)
            if isinstance(obj, ast.Call):
                if isinstance(obj.func, ast.Attribute):
                    if not isinstance(obj.func.value, ast.Name) or obj.func.value.id != '_':
                        raise self._err(obj, 'Can only call attributes from _ (ie. `_.mtc0(a, b)`)')
                    cmd = obj.func.attr
                    if cmd not in self.custom_commands:
                        raise AttributeError("No such custom function '{}'".format(cmd))
                    return self.custom_commands[cmd](*(self.resolve(arg) for arg in obj.args))
                elif not isinstance(obj.func, ast.Name):
                    raise self._err(obj, 'Functions can only be called by name')
                self.find_var(obj.func.id)  # Ensures function is defined

                for context in self.stack:
                    context.mark_func_call(self.cur_line)

                for i, arg in enumerate(obj.args):
                    self.assign(self.new_var(reg='a' + str(i)), self.resolve(arg), obj=arg)
                self.inst('jal', obj.func.id, obj=obj)
                return_var = self.new_var(reg='v0')
                out_var = self.new_var()
                self.assign(out_var, return_var, obj=obj)
                return out_var
            if isinstance(obj, ast.UnaryOp):
                op = obj.op
                target = self.resolve(obj.operand)
                if target.num is not None:
                    opera = ast.Num(self.constants.get(target.num, target.num))
                    opera.lineno = 0
                    opera.col_offset = 0
                    op = ast.UnaryOp(op, opera)
                    op.lineno = 0
                    op.col_offset = 0
                    exp = ast.Expression(op)
                    exp.lineno = 0
                    code = compile(exp, '', mode='eval')
                    return self.new_var(num=eval(code))
                if isinstance(op, ast.USub):
                    var = self.new_var()
                    var.typ = target.typ
                    v = self.new_var(num=-1)
                    self.inst('mul', var, target, v, reads=[target], writes=[var], imm=('mul', v))
                elif isinstance(op, ast.Invert):
                    var = self.new_var()
                    var.typ = target.typ
                    self.inst('not', var, target, reads=[target], writes=[var], imm=('not', target))
                elif isinstance(op, ast.UAdd):
                    var = target
                else:
                    raise self._err(op, 'Unsupported unary operationr {} (line {} col {})')
                return var
            if isinstance(obj, ast.BinOp):
                left_val = self.resolve(obj.left)
                right_val = self.resolve(obj.right)
                op_to_inst = {
                    ast.Mult: ('mul', 'mul'),
                    ast.Add: ('add', 'addi'),
                    ast.Sub: ('sub', 'sub'),
                    ast.BitAnd: ('and', 'andi'),
                    ast.BitOr: ('or', 'ori'),
                    ast.BitXor: ('xor', 'xori'),
                    ast.RShift: ('srl', 'srl'),
                    ast.LShift: ('sllv', 'sll')
                }
                var = self.new_var()
                inst, im_inst = op_to_inst[type(obj.op)]

                if left_val.num is not None and right_val.num is not None:
                    num1 = ast.Num(self.constants.get(left_val.num, left_val.num))
                    num2 = ast.Num(self.constants.get(right_val.num, right_val.num))
                    op = ast.BinOp(num1, obj.op, num2)
                    exp = ast.Expression(op)
                    exp.lineno = op.lineno = num1.lineno = num2.lineno = 0
                    exp.col_offset = op.col_offset = num1.col_offset = num2.col_offset = 0
                    return self.new_var(num=eval(compile(exp, '', mode='eval')))
                if left_val.num is not None:
                    if inst in ['sub', 'srv', 'sllv']:
                        old_num = left_val
                        left_val = self.new_var()
                        self.assign(left_val, old_num)
                    else:
                        left_val, right_val = right_val, left_val
                if type(obj.op) not in op_to_inst:
                    raise self._err(obj.op, 'Unsupported operator {} at line {} col {}.')

                var.typ = var.typ or left_val.typ or right_val.typ
                self.inst(inst, var, left_val, right_val, reads=[left_val, right_val], writes=[var], obj=obj,
                          imm=(im_inst, right_val))
                return var
            if isinstance(obj, ast.Name):
                return self.find_var(obj.id)

            raise self._err(obj, 'Unsupported {} expression syntax at line {} col {}.')
        finally:
            self.pop_stack()

    def inst(self, inst, *args, reads=None, writes=None, obj=None, imm=None, fmt=None):
        if inst in ['sub', 'add'] and args[2].num == 0:
            self.assign(args[0], args[1], obj)
            return
        if inst == 'mul' and args[2].num == 1:
            self.assign(args[0], args[1], obj)
            return
        if inst == 'mul' and args[2].num == 0:
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
            array = self.resolve(target.value)
            if not isinstance(target.slice, ast.Index):
                raise self._err(target.slice)
            if isinstance(target.slice.value, ast.Tuple):
                index = None
            else:
                index = self.resolve(target.slice.value)
            try:
                offs = array.get_byte_offset()
            except TypeError as e:
                print('No type defined for {} variable (line {} col {}).'.format(target.value, obj.lineno,
                                                                                 obj.col_offset),
                      file=sys.stderr)  # TODO: Make error
                array.typ = Types.INTS
                offs = 1
            typ = array.typ
            inst = {Types.INTS: 'sw', Types.BYTES: 'sb'}[typ]
            if index and index.num is not None:
                byt_of = self.new_var(num=index.num * offs)
                self.inst(inst, value, byt_of, array, fmt='{}, {}({})', reads=[value, byt_of, array], writes=[],
                          obj=obj)
            else:
                if index:
                    offset = self.new_var()
                    self.assign(offset, index, obj)
                    byt_mul = self.new_var(num=offs)
                    self.inst('mul', offset, offset, byt_mul, reads=[offset, byt_mul], writes=[offset], obj=obj, imm=('mul', byt_mul))
                    self.inst('add', offset, offset, array, reads=[offset, index], writes=[offset], obj=obj, imm=('addi', array))
                    memloc = offset
                else:
                    memloc = array
                self.inst(inst, value, 0, memloc, reads=[value, memloc], writes=[], fmt='{}, {}({})', obj=obj)
        else:
            raise self._err(target)

    def handle_assign(self, obj: ast.Assign):
        read_var = self.resolve(obj.value)
        for target in obj.targets:
            self.assign_target(target, read_var, obj)

    def handle_augassign(self, obj: ast.AugAssign):
        self.assign_target(obj.target, self.resolve(ast.BinOp(obj.target, obj.op, obj.value)), obj)

    def handle_if(self, obj: ast.If):
        if len(obj.body) == 1:
            statm = obj.body[0]
            if isinstance(statm, ast.Continue):
                self.branch_compare(obj.test, self.cur_label, True)
                return
            elif isinstance(statm, ast.Return) and obj.body[0].value is None:
                self.branch_compare(obj.test, self.cur_label + '_end', True)
                return
        end_label = self.get_label('_skip_if')
        self.branch_compare(obj.test, end_label, False)
        self.mark_obj(obj)
        for i in obj.body:
            self.interpret(i)
        self.add(Label(end_label))

    def branch_compare(self, obj: ast.AST, jump_label, jump_condition):
        if not isinstance(obj, ast.Compare):
            val = self.resolve(obj)
            self.inst('bnez' if jump_condition else 'beqz', val, jump_label, reads=[val], obj=obj)
            return
        op = type(obj.ops[0])
        left_var = self.resolve(obj.left)
        right_var = self.resolve(obj.comparators[0])

        if jump_condition:
            eq_op_to_inst = {
                ast.Eq: 'beq',
                ast.NotEq: 'bne'
            }
            cp_op_to_inst = {
                ast.Lt: 'bltz',
                ast.LtE: 'blez',
                ast.Gt: 'bgtz',
                ast.GtE: 'bgez'
            }
        else:
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
            self.inst(eq_op_to_inst[op], left_var, right_var, jump_label, reads=[left_var, right_var], obj=obj)
        elif op in cp_op_to_inst:
            a_minus_b = self.resolve(ast.BinOp(obj.left, ast.Sub(), obj.comparators[0]))
            self.inst(cp_op_to_inst[op], a_minus_b, jump_label, reads=[a_minus_b], writes=[], obj=obj)
        else:
            raise self._err(obj.ops[0], 'Unsupported {} condition at line {} col {}.')

    def mark_obj(self, obj: ast.AST):
        """Provides a more accurate object marker for the last command"""
        self.inst('nop', reads=self.lines[-1].writes, obj=obj)

    def handle_while(self, obj: ast.While):
        if obj.orelse:
            raise self._err(obj.orelse)
        self.push_stack()
        self.push_label(obj, 'while', '_end')
        label = self.cur_label
        end_label = label + '_end'
        self.add(Label(label))
        exp = obj.test
        if not isinstance(exp, ast.Compare) or len(exp.comparators) != 1:
            raise self._err(exp)

        self.branch_compare(exp, end_label, False)
        self.mark_obj(obj)

        for i in obj.body:
            self.interpret(i)

        self.inst('j', label, reads=[], writes=[])
        self.add(Label(end_label))
        self.pop_label()
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
            self.assign(return_var, expr_val, obj)
        self.inst('j', parent_func_label + '_end', obj=obj)

    def handle_expr(self, obj: ast.Expr):
        if isinstance(obj.value, ast.Str):
            self.lines.extend(obj.value.s.strip().split('\n'))
        else:
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
    parser.add_argument('-d', '--debug', action='store_true', help='Add debug output')
    args = parser.parse_args()

    if not args.input_files and sys.stdin.isatty():
        parser.error('Please specify input files or pass input via stdin')

    lines = []

    for src in args.input_files:
        with open(src) as f:
            lines.extend(FuncGenerator.generate(f.read(), src, args.debug))
    if not args.input_files:
        lines.extend(FuncGenerator.generate(sys.stdin.read(), '<stdin>', args.debug))

    if args.output:
        with open(args.output, 'w') as f:
            f.write('\n'.join(lines))
    else:
        print('\n'.join(lines))


if __name__ == '__main__':
    main()
