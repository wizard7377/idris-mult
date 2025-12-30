Inductive mu : forall (n : nat) , forall (t : Type) , forall (w : t) , Type :=
  | mz : forall {t w}, mu 0 t w
                   | ms : forall {n t} , forall (w : t) , mu n t w -> mu (S n) t w
                                                              .

Search mu.
