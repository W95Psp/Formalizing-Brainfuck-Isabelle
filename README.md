# Formalizing-Brainfuck-Isabelle
Fibonaci implemented in brainfuck and formalized in isabelle and some other stuff 

## Fibonacci version
Very simple one, modulo 256
```
+>>+<<            <<++++++[->>
   [<+>>+<-] < [->+<] >       >> [->+<] > [-<<<+>>>] << [->+<] <.
<<]
```
"Fields" used: `[_C_|_a'_|_a_|_a"_|_b_|_b'_]`, where x' is a copy of x, and C the number of iterations

Test it with https://htmlpreview.github.io/?https://raw.githubusercontent.com/W95Psp/Formalizing-Brainfuck-Isabelle/master///Interpreteur%20BF.html
