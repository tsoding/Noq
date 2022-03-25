# Noq

Not [Coq](https://coq.inria.fr/). Simple expression transformer that is not Coq.

## Quick Start

```console
$ cargo run
```

## Main Idea

The Main Idea is being able to define transformation rules of symbolic algebraic expressions and sequentially applying them.

### Transforming the derivative of square function

*(WARNING! This is not a working example yet!)*

```
rule square_def    square(x) = x^2;
rule parens        (a) - b = a - b
rule swap          a + b - c = a - c + b
rule swap_sum      a + b = b + a
rule sub           a - a = 0
rule sum_id        0 + a = a
rule lim_replace   lim(var, value, expr) = #replace(var, value, expr)
rule div_distrib   (a + b) / c = a / c + b / c

rule square_of_sum (x + y)^2 = x^2 + 2*x*y + y^2;
rule der_def       der(f) = lim(dx, 0, (f(x + dx) - f(x)) / dx);

shape der(square)                  // der(square)
  apply all der_def                // lim(dx, 0, (square(x + dx) - square(x)) / dx)
  apply all square_def             // lim(dx, 0, ((x + dx)^2 - x^2) / dx)
  apply all square_of_sum          // lim(dx, 0, ((x^2 + 2*x*dx + dx^2) - x^2) / dx)
  apply all parens                 // lim(dx, 0, (x^2 + 2*x*dx + dx^2 - x^2) / dx)
  apply all swap                   // lim(dx, 0, (x^2 + 2*x*dx - x^2 + dx^2) / dx)
  apply all swap                   // lim(dx, 0, (x^2 - x^2 + 2*x*dx + dx^2) / dx)
  apply all sub                    // lim(dx, 0, (0 + 2*x*dx + dx^2) / dx)
  apply all sum_id                 // lim(dx, 0, (2*x*dx + dx^2) / dx)
  apply all div_distrib            // lim(dx, 0, (2*x*dx) / dx + (dx^2) / dx)
  apply all rule (a^2) / a = a     // lim(dx, 0, (2*x*dx) / dx + dx)
  apply all rule (a*b*c) / c = a*b // lim(dx, 0, 2*x + dx)
  apply all lim_replace            // 2*x + 0
  apply all swap_sum               // 0 + 2*x
  apply all sum_id                 // 2*x
done
```
