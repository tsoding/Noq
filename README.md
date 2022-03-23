# Noq

Not [Coq](https://coq.inria.fr/). Simple expression transformer that is not Coq.

## Quick Start

```console
$ cargo run
```

## Main Idea

The Main Idea is being able to define transformation rules of symbolic algebraic expressions and sequentially applying them.

### Transforming the derivative of square function

```
square_of_sum : (x + y)^2 = x^2 + 2*x*y + y^2;
der_def       : der(f) = lim(dx, 0, (f(x + dx) - f(x)) / dx);
square_def    : square(x) = x^2;
parens        : (a) - b = a - b
swap          : a + b - c = a - c + b
swap_sum      : a + b = b + a
sub           : a - a = 0
sum_id        : 0 + a = a
lim_replace   : lim(var, value, expr) = #replace(var, value, expr)
div_distrib   : (a + b) / c = a / c + b / c
foo           : (a^2) / a = a
bar           : (a*b*c) / c = a*b

Transform(der(square))
| apply_all(der_def)       => lim(dx, 0, (square(x + dx) - square(x)) / dx)
| apply_all(square_def)    => lim(dx, 0, ((x + dx)^2 - x^2) / dx)
| apply_all(square_of_sum) => lim(dx, 0, ((x^2 + 2*x*dx + dx^2) - x^2) / dx)
| apply_all(parens)        => lim(dx, 0, (x^2 + 2*x*dx + dx^2 - x^2) / dx)
| apply_all(swap)          => lim(dx, 0, (x^2 + 2*x*dx - x^2 + dx^2) / dx)
| apply_all(swap)          => lim(dx, 0, (x^2 - x^2 + 2*x*dx + dx^2) / dx)
| apply_all(sub)           => lim(dx, 0, (0 + 2*x*dx + dx^2) / dx)
| apply_all(sum_id)        => lim(dx, 0, (2*x*dx + dx^2) / dx)
| apply_all(div_distrib)   => lim(dx, 0, (2*x*dx) / dx + (dx^2) / dx)
| apply_all(foo)           => lim(dx, 0, (2*x*dx) / dx + dx)
| apply_all(bar)           => lim(dx, 0, 2*x + dx)
| apply_all(lim_replace)   => 2*x + 0
| apply_all(swap_sum)      => 0 + 2*x
| apply_all(sum_id)        => 2*x
```
