type nat =
  | Z
  | S of nat

type list =
  | Nil
  | Cons of nat * list

let rec list_snoc : list -> nat -> list |>
/\([ ]       -> /\(0 ->          [0], 1 ->          [1]),
   [0]       -> /\(0 ->       [0; 0], 1 ->       [0; 1]),
   [1; 0]    -> /\(0 ->    [1; 0; 0], 1 ->    [1; 0; 1])) = ?

; It cannot be done polymorphically