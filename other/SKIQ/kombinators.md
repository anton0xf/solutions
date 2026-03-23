# Chapter 6: The Joy Of Jay
## 6.1 Enter Jay
Build the J combinator: `J a b c d = a b (a d c)`
```
J f x y z = f x (f z y)
          = x `f` (z `f` y)
J = f -> x -> y -> z -> f x (f z y)
J = S(S(KS)(S(K(S(KS)))(S(K(S(KK)))(S(K(S(KS)))(S(KK)))))) (S(KK)(S(S(KS)(S(KK)S))(KK)))
```

## 6.2 Swap [IJ]
Implement `T x y = y x` with just J and I.
```
T = JII
  = y -> z -> [f x (f z y) / f = I, x = I]
  = y -> z -> I I (I z y)
  = y -> z -> z y

I f x = f x
T x f = f x
```

## 6.3 The missing link [IJ]
Implement the Quixotic bird: `Q1 x y z = x (z y)`.
```
Q1 = JI
q1 = f -> x -> g -> f (g x)
q1 f x g = f (g x)
q1 I = T
```

```
JT = J(JII)= R
P = J q1 = J(JI) = g -> y -> h -> q1 g (q1 h y)
q1 g (q1 h y) = u -> g (u (v -> h (v y)))
P g y h u = g (u (v -> h (v y)))
P f x g k = f (k (v -> g (v x)))

q2 = J q1 T = J(JI)(JII)
q2 x f g = f (g x)

q1 J x g = J (g x)
  = t y z -> g x t (g x z y)

q1 T x f = T (f x)
  = g -> g (f x)
q1 T x f g = g (f x)
q3 = q1 T
q3 x f g = g (f x)

```

## 6.4 B patient [IJ]
Implement `B x y z = x (y z)` with just J and I.
```
R a b c = b c a
R = JT
R = a -> b -> c -> b c a

B f g x = f (g x)
  = q1 f x g
  = R g (q1 f) x
B f g = R (q1 f) R g

B f = R (q1 f) R
  = RRR (q1 f)
  = R q1 (q1 (RRR)) f
B = JT(JI)(JI(JT(JT)(JT)))
  = J(JII)(JI)(JI(J(JII)(J(JII))(J(JII))))

B f = R (q1 f) R
  = RR (R q1 (q1 R)) f

C = RRR
B = C(JIC)(JI)
  = JT(JT)(JT)(JI(JT(JT)(JT)))(JI)
  = J(JII)(J(JII))(J(JII))(JI(J(JII)(J(JII))(J(JII))))(JI)
```

```
J f x y z = f x (f z y)
T x f = f x
q1 f x g = f (g x)
q2 x f g = f (g x)
q3 x g f = f (g x)
```

## 6.5 C in J [IJ]
Now that you have both B and T, C can be made, for sure.
However, maybe you'll find a simpler expression...
```
C a b c = a c b
C f y x = f x y
C = RRR
  = JT(JT)(JT)
  = J(JII)(J(JII))(J(JII))
```

## 6.6 Duplication [IJ]
Duplication is somewhat trickier as the only duplicated argument (a) in J only appears on the left hand side of something else. Still it is possible.
Implement W x y = x y y with just J and I.
```
W f x = f x x
  = T x (T x f)
  = T x T (T x T f)
  = (T x) T ((T x) T f)
  = J (T x) T f T
  = B (RT(R f (RTJ))) T x
W = B(q1(B(RTB)(RT))(RTJ))R
  = (J(JII)(JI)(JI(J(JII)(J(JII))(J(JII)))))(JI((J(JII)(JI)(JI(J(JII)(J(JII))(J(JII)))))(J(JII)(JII)(J(JII)(JI)(JI(J(JII)(J(JII))(J(JII))))))(J(JII)(JII)))(J(JII)(JII)J))(J(JII))
```
