module Core.Hint

val black_box: #a:Type0 -> x:a -> y:a{y == x}
val must_use: #t:Type0 -> x:t -> y:t{y == x}
