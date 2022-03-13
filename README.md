# Nested-abstract-syntax-based-lambda-calculus
a simple way to get rid of bound variables issues.

This coq program compiles with coq 8.7 (at least) and defines untyped lambda calculus using a very simple idea for
implementing bound variables, similar to locally nameless convention.

Here is the idea in a nutshell: option is an operation that takes a set (or a type) and add exactly one element to  it.
Starting from this, if C is any set, we define inductively a lambda term with variables in C as
-an element of C
-the application of x on y, where x, y are lambda terms with variables in C
-the abstraction of a lambda term with variables in option(C) (the new element in option(C) is playing the role of a new variable)
Open the .html file with your favorite web browser for more information.
