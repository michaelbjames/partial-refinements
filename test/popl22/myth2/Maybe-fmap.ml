type 'a maybe =
  | Nothing
  | Just of 'a

let maybe_fmap : (('a -> 'b) -> 'a maybe -> 'b maybe) |>
    (a1 -> b1) -> /\(Nothing -> Nothing,
                    Just a1 -> Just b1) =?