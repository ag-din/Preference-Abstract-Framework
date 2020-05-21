# Preference Abstract Framework Python Implementation

This repository contains a Python implementation of a Preference Abstract Framework (PAF) proposed by Amgoud & Cayrol in 2002 read the following article:
```
Amgoud&Cayrol.2002.pdf
```
To test the implementation run the example in example-PAF.py file:
```
python example-PAF.py
```
The set of arguments *A*, the set of attack relationships *attacks* between the arguments, and a preference relationship *Pref* must be specified. Example:
```
A = {"a", "b", "c"}
attacks = {("b", "c"), ("c", "a")}
Pref = [(["b"], ["c"])]
```
In this example, a tuple like ("b", "c") represents an attack: "b" represents an attack against "c". Also, [(["b"], ["c"])] represents "b" is preferred to "c".

In general there are 3 class of argument in PAF = (A, attacks, Pref):
* Class of acceptable arguments (nondefeated arguments)
* Class of rejected arguments (arguments defeated)
* Class of arguments in abeyance (neither acceptable nor rejected)

Four acceptability semantics were implemented:
* Stable
* Complete
* Grounded
* Preferred

For each argument *a* in *A* we can define its status under a given semantics:
* Skeptically accepted
* Credulously accepted
* Rejected

Finally, there are some unit tests for each piece of code in testing-PAF.py.
```
python testing-PAF.py
```
