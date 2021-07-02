type nat =
  | Z
  | S of nat

type list =
  | Nil
  | Cons of nat * list

let rec add (n1:nat) (n2:nat) : nat =
  match n1 with
  | Z u -> n2
  | S n1 -> S (add n1 n2)
;;

let rec list_sum : list -> nat |>
/\([] -> 0,
  [1;2] -> 3,
  [2] -> 2) = ?
