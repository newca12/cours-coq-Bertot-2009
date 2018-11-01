Require Import List.

Print list.

About cons.

Check cons 3.

Check cons 3 nil.

About nil.

Check (nil : list nat).

Compute match (3::2::1::nil) with nil => true | a :: l' => false end.

Compute match (nil : list nat) with nil => true | a :: l' => false end.

Compute match (3::2::1::nil) with nil => 0 | a :: l' => a end.

Compute match (3::2::1::nil) with nil => nil | a :: l' => l' end.

Fixpoint sum_l l := match l with nil => 0 | a :: l' => a + sum_l l' end.

Check sum_l.

Compute sum_l (3::2::1::nil).

Compute match S (S O) with O => true | S p => false end.

Compute match O with O => true | S p => false end.

Compute match S (S O) with O => O | S p => p end.

Compute match O with O => O | S p => p end.

