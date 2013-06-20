Declare ML Module "tacfork".

Goal True /\ False /\ True /\ True.
Proof.
repeat apply conj; fork idtac >> eauto.
Qed.
