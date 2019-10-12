# Reamit

*Readable assembly code generator*

Whether for learning or for optimized code, often we want to write readable
assembly that's close to the user-defined behavior. That's where Reamit comes it.
It's a programming language based on a subset of Python that maps almost directly
to assembly. Right now, only MIPS is supported.

## Installation

Install via [PyPI](https://pypi.org/project/reamit/):

```bash
pip3 install --user reamit
```

## Usage

Use via the `reamit` command:

```bash
reamit -o output.s input.rm
```

*Note:* `.rm` is a new extension for the Reamit language which closely resembles Python.


## Examples

`simple.py`:

```python
def sum_to_n(n: int) -> int:
    num = 0
    total = 0
    while num <= n:
        total += num
    return total
```

`simple.s`:

```s
sum_to_n:
	li	$t0, 0	# num = 0
	li	$v0, 0	# total = 0

sum_to_n_while:
	sub	$t1, $t0, $a0	# num <= n:
	bgtz	$t1, sum_to_n_while_end	# num <= n:
	add	$v0, $v0, $t0	# total += num

sum_to_n_while_end:

sum_to_n_end:
	jr	$ra
```

`factorial.rm`:
```python
def factorial(n: int) -> int:
    if n == 0:
        return 1
    return n * factorial(n - 1)`
```

`factorial.s`:
```s
factorial:
	sub	$sp, 8	# Allocate stack
	sw	$ra, 0($sp)
	sw	$s0, 4($sp)

	# === Arguments ===
	move	$s0, $a0	# n

	bne	$s0, 0, factorial_skip_if	# n == 0:
	li	$v0, 1	# return 1
	j	factorial_end	# return 1

factorial_skip_if:
	sub	$a0, $s0, 1	# n - 1
	jal	factorial	# factorial(n - 1)
	move	$t0, $v0	# factorial(n - 1)
	mul	$v0, $s0, $t0	# n * factorial(n - 1)

factorial_end:
	lw	$s0, 4($sp)
	lw	$ra, 0($sp)
	add	$sp, 8	# Deallocate stack
	jr	$ra
```
