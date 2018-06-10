# match

I always forget the syntax for matching. Here are loads of examples, taken from TPIL.

### Examples

```lean
open nat

def sub1 : ℕ → ℕ
| zero     := zero
| (succ x) := x


def is_zero : ℕ → Prop
| 0     := true
| (x+1) := false
```
(last one works because addition and zero are tagged `[pattern]`).

Cool unravelling:
```lean
def foo : ℕ × ℕ → ℕ
| (m, n) := m + n
```


Matching everything in cool ways:

```lean
def sub2 : ℕ → ℕ
| zero            := 0
| (succ zero)     := 0
| (succ (succ a)) := a


def band : bool → bool → bool
| tt a := a
| ff _ := ff
```

Whether you're before or after the colon makes a difference:

```lean
def tail1 {α : Type u} : list α → list α
| []       := []
| (h :: t) := t

def tail2 : Π {α : Type u}, list α → list α
| α []       := []
| α (h :: t) := t
```

That `match with` version:

```lean
def is_not_zero (m : ℕ) : bool :=
match m with
| 0     := ff
| (n+1) := tt
end
```

You can match several things if you get the commas right

```lean
def foo (n : ℕ) (b c : bool) :=
5 + match n - 5, b && c with
    | 0,      tt := 0
    | m+1,    tt := m + 7
    | 0,      ff := 5
    | m+1,    ff := m + 3
    end
```