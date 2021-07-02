type bool =
  | True
  | False

type nat =
  | Z
  | S of nat

type neg =
  | NegOne
  | NegSucc of neg

type num =
  | Nat of nat
  | Neg of neg

type list =
  | Nil
  | Cons of num * list

let rec all_neg : list -> bool |>
/\([]                  -> True,
   [Nat Z]             -> False,
   [Neg (NegSucc (NegOne));Neg (NegOne)] -> True,
   [Neg (NegSucc (NegOne));Nat (Z)] -> False,
   [Neg (NegOne)] -> True) = ?