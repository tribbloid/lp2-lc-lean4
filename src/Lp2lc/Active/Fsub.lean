
namespace Lp2lc.Active.Fsub

-- Coq: Lp2lc_coq\Active\Fsub.v:430-436
theorem open_tt_rec_type_core (T : typ) (j : Nat) (V U : typ) (i : Nat) (h : i ≠ j) : type U → type (open_tt_rec j V T) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:438-445
theorem open_tt_rec_type (T U : typ) : type U → type (open_tt T U) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:447-454
theorem subst_tt_fresh (Z : String) (U T : typ) : Z ∉ fv_tt T → subst_tt Z U T = T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:456-464
theorem subst_tt_open_tt_rec (T1 T2 X P : typ) (n : Nat) : type P → subst_tt X P (open_tt_rec n T1 T2) = open_tt_rec n (subst_tt X P T1) (subst_tt X P T2) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:466-474
theorem subst_tt_open_tt (T1 T2 X P : typ) : type P → subst_tt X P (open_tt T1 T2) = open_tt (subst_tt X P T1) (subst_tt X P T2) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:476-484
theorem subst_tt_open_tt_var (X Y : String) (U T : typ) : Y ≠ X → type U → subst_tt X U (open_tt T (var (Nat.ofString Y))) = open_tt (subst_tt X U T) (var (Nat.ofString Y)) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:486-496
theorem subst_tt_intro (X : String) (T2 U : typ) : X ∉ fv_tt T2 → type U → open_tt (subst_tt X U T2) U = T2 := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:498-503
theorem open_te_rec_term_core (e : trm) (j : Nat) (u : trm) (i : Nat) (P : Prop) : term u → term (open_te_rec j u e) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:505-512
theorem open_te_rec_type_core (e : trm) (j : Nat) (Q : typ) (i : Nat) (P : Prop) : i ≠ j → type Q → type (open_te_rec j Q e) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:514-525
theorem open_te_rec_term (e : trm) (U : typ) : term e → type U → term (open_te e U) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:527-533
theorem subst_te_fresh (X : String) (U : typ) (e : trm) : X ∉ fv_te e → subst_te X U e = e := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:535-544
theorem subst_te_open_te (e : trm) (T X : String) (U : typ) : type U → subst_te X U (open_te e (var (Nat.ofString T))) = open_te (subst_te X U e) (subst_tt X U (var (Nat.ofString T))) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:546-554
theorem subst_te_open_te_var (X Y : String) (U : typ) (e : trm) : Y ≠ X → type U → subst_te X U (open_te e (var (Nat.ofString Y))) = open_te (subst_te X U e) (var (Nat.ofString Y)) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:556-566
theorem subst_te_intro (X : String) (U : typ) (e : trm) : X ∉ fv_te e → type U → open_te (subst_te X U e) U = e := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:568-574
theorem open_ee_rec_term_core (e : trm) (j : Nat) (v u : trm) (i : Nat) : i ≠ j → term u → term (open_ee_rec j v e) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:576-581
theorem open_ee_rec_type_core (e : trm) (j : Nat) (V : typ) (u : trm) (i : Nat) : term u → type (open_ee_rec j u e) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:583-593
theorem open_ee_rec_term (u e : trm) : term u → term e → term (open_ee e u) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:595-602
theorem subst_ee_fresh (x : String) (u e : trm) : x ∉ fv_ee e → subst_ee x u e = e := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:604-614
theorem subst_ee_open_ee (t1 t2 u : trm) (x : String) : term u → subst_ee x u (open_ee t1 t2) = open_ee (subst_ee x u t1) (subst_ee x u t2) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:616-624
theorem subst_ee_open_ee_var (x y : String) (u e : trm) : y ≠ x → term u → subst_ee x u (open_ee e (var (Nat.ofString y))) = open_ee (subst_ee x u e) (var (Nat.ofString y)) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:626-635
theorem subst_ee_intro (x : String) (u e : trm) : x ∉ fv_ee e → term u → open_ee (subst_ee x u e) u = e := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:637-645
theorem subst_te_open_ee_var (Z : String) (P : typ) (x : String) (e : trm) : term P → x ≠ Z → subst_te Z P (open_ee e (var (Nat.ofString x))) = open_ee (subst_te Z P e) (var (Nat.ofString x)) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:647-655
theorem subst_ee_open_te_var (z : String) (u : trm) (e : trm) (X : String) : term u → X ∉ fv_te e → subst_ee z u (open_te e (var (Nat.ofString X))) = open_te (subst_ee z u e) (var (Nat.ofString X)) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:657-663
theorem subst_tt_type (T : typ) (Z : String) (P : typ) : type T → type P → type (subst_tt Z P T) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:665-671
theorem subst_te_term (e : trm) (Z : String) (P : typ) : term e → type P → term (subst_te Z P e) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:673-688
theorem subst_ee_term (e1 : trm) (Z : String) (e2 : trm) : term e1 → term e2 → term (subst_ee Z e2 e1) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:690-696
theorem wft_type (E : env) (T : typ) : wft E T → type T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:698-711
theorem wft_weaken (G : env) (T : typ) (E F : env) : wft (E ++ G) T → okt F → wft (E ++ F ++ G) T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:713-728
theorem wft_narrow (V U T : typ) (F E : env) (X : String) : wft (E ++ (X, bind.sub U) :: F) V → sub E U T → wft (E ++ (X, bind.sub T) :: F) V := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:730-745
theorem wft_strengthen (E F : env) (x : String) (U T : typ) : wft (E ++ (x, bind.typ U) :: F) T → sub E U T → wft (E ++ F) T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:747-771
theorem wft_subst_tb (F Q E : env) (Z : String) (P T : typ) : wft (E ++ (Z, bind.typ P) :: F) Q → wft E P → wft (E ++ F) (subst_tt Z P Q) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:773-793
theorem wft_open (E : env) (U T1 T2 : typ) : wft E U → wft (E ++ ("_", bind.sub U) :: []) T1 → (∀ X, wft (E ++ (X, bind.sub U) :: []) T2) → wft E (open_tt T1 T2) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:795-803
theorem ok_from_okt (E : env) : okt E → List.Sorted (· < ·) (E.keys) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:805-822
theorem wft_from_env_has_sub (x : String) (U E : env) : List.lookup x E = some (bind.sub U) → wft E U := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:824-841
theorem wft_from_env_has_typ (x : String) (U E : env) : List.lookup x E = some (bind.typ U) → wft E U := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:843-850
theorem wft_from_okt_typ (x : String) (T : typ) (E : env) : okt E → List.lookup x E = some (bind.typ T) → wft E T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:852-861
theorem wft_from_okt_sub (x : String) (T : typ) (E : env) : okt E → List.lookup x E = some (bind.sub T) → wft E T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:863-880
theorem wft_weaken_right (T : typ) (E F : env) : wft E T → okt F → wft (E ++ F) T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:882-889
theorem okt_push_inv (E : env) (X : String) (B : bind) : okt ((X, B) :: E) → okt E ∧ X ∉ E.keys := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:891-898
theorem okt_push_sub_inv (E : env) (X : String) (T : typ) : okt ((X, bind.sub T) :: E) → okt E ∧ X ∉ E.keys := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:900-902
theorem okt_push_sub_type (E : env) (X : String) (T : typ) : okt ((X, bind.sub T) :: E) → wft E T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:904-911
theorem okt_push_typ_inv (E : env) (x : String) (T : typ) : okt ((x, bind.typ T) :: E) → okt E ∧ x ∉ E.keys := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:913-919
theorem okt_push_typ_type (E : env) (X : String) (T : typ) : okt ((X, bind.typ T) :: E) → wft E T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:921-936
theorem okt_narrow (V : typ) (E F : env) (U X : String) : okt (E ++ (X, bind.sub U) :: F) → sub E U V → okt (E ++ (X, bind.sub V) :: F) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:938-952
theorem okt_strengthen (x : String) (T : typ) (E F : env) : okt (E ++ (x, bind.typ T) :: F) → sub E U T → okt (E ++ F) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:954-977
theorem okt_subst_tb (Q : typ) (Z : String) (P : typ) (E F : env) : okt (E ++ (Z, bind.typ P) :: F) → wft E P → okt (E ++ F) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:979-987
theorem notin_fv_tt_open (Y X : String) (T : typ) : Y ∉ fv_tt T → open_tt T (var (Nat.ofString Y)) = T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:989-997
theorem notin_fv_wf (E : env) (X : String) (T : typ) : wft E T → X ∉ fv_tt T → wft (E ++ (X, bind.sub T) :: []) T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:999-1012
theorem map_subst_tb_id (G : env) (Z : String) (P : typ) : (∀ x, List.lookup x G = none) → wft G P → List.map (subst_tb Z P) G = G := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1014-1023
theorem sub_regular (E : env) (S T : typ) : sub E S T → wft E S ∧ wft E T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1025-1060
theorem typing_regular (E : env) (e : trm) (T : typ) : typing E e T → term e ∧ wft E T ∧ okt E := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1062-1068
theorem value_regular (t : trm) : value t → term t := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1070-1120
theorem red_regular (t t' : trm) : red t t' → term t ∧ term t' := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1122-1133
theorem sub_reflexivity (E : env) (T : typ) : wft E T → sub E T T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1135-1150
theorem sub_weakening (E F G : env) (S T : typ) : sub (E ++ G) S T → okt F → sub (E ++ F ++ G) S T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1152-1157
definition transitivity_on (Q : env → typ → typ → Prop) := ∀ E S T, Q E S T → Q E T S → Q E S S

-- Coq: Lp2lc_coq\Active\Fsub.v:1159-1181
theorem sub_narrowing_aux (Q : env → typ → typ → Prop) (F E : env) (Z : String) (P S T : typ) : (∀ E S T, sub E S T → Q E S T) → wft (E ++ (Z, bind.sub P) :: F) S → wft (E ++ (Z, bind.sub P) :: F) T → Q (E ++ (Z, bind.sub S) :: F) T S := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1183-1201
theorem sub_transitivity (Q : env → typ → typ → Prop) : (∀ E S T, sub E S T → Q E S T) → transitivity_on Q := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1203-1216
theorem sub_narrowing (Q E F : env) (Z : String) (P S T : typ) : sub (E ++ (Z, bind.sub P) :: F) S T → sub E P S → sub (E ++ (Z, bind.sub T) :: F) S T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1218-1252
theorem sub_through_subst_tt (Q E F : env) (Z S T P : typ) : wft (E ++ (Z, bind.typ P) :: F) S → wft (E ++ (Z, bind.typ P) :: F) T → wft E P → sub (E ++ F) (subst_tt Z P S) (subst_tt Z P T) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1254-1271
theorem typing_weakening (E F G : env) (e : trm) (T : typ) : typing (E ++ G) e T → okt F → typing (E ++ F ++ G) e T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1273-1286
theorem sub_strengthening (x : String) (U E F S T : typ) : sub (E ++ (x, bind.typ U) :: F) S T → sub E U S → sub (E ++ F) S T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1288-1304
theorem typing_narrowing (Q E F : env) (X : String) (P e T : typ) : typing (E ++ (X, bind.sub P) :: F) e T → sub E P Q → typing (E ++ (X, bind.sub Q) :: F) e T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1306-1327
theorem typing_through_subst_ee (U E F : env) (x T e u : trm) : typing (E ++ (x, bind.typ U) :: F) e T → typing E u U → typing (E ++ F) (subst_ee x u e) T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1329-1357
theorem typing_through_subst_te (Q E F : env) (Z e T P : typ) : typing (E ++ (Z, bind.typ P) :: F) e T → wft E P → typing (E ++ F) (subst_te Z P e) (subst_tt Z P T) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1359-1369
theorem typing_inv_abs (E : env) (S1 e1 : trm) (T : typ) : typing E (abs S1 e1) T → ∃ T2, T = arr S1 T2 ∧ (∀ x, typing ((x, bind.typ S1) :: E) e1 T2) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1371-1389
theorem typing_inv_tabs (E : env) (S1 e1 : trm) (T : typ) : typing E (tabs S1 e1) T → ∃ T2, T = all S1 T2 ∧ (∀ X, typing ((X, bind.sub S1) :: E) e1 T2) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1391-1424
theorem preservation_result : preservation := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1426-1437
theorem canonical_form_abs (t U1 U2 : typ) : value t → typing [] t (arr U1 U2) → ∃ e, t = abs U1 e := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1439-1453
theorem canonical_form_tabs (t U1 U2 : typ) : value t → typing [] t (all U1 U2) → ∃ e, t = tabs U1 e := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1455-1455
theorem progress_result : progress := by sorry

namespace Lp2lc.Active.FsubL_alt

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:464-470
theorem open_tt_rec_type_core (T : typ) (j : Nat) (V U : typ) (i : Nat) (h : i ≠ j) : type U → type (open_tt_rec j V T) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:472-479
theorem open_tt_rec_type (T U : typ) : type U → type (open_tt T U) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:481-488
theorem subst_tt_fresh (Z : String) (U T : typ) : Z ∉ fv_tt T → subst_tt Z U T = T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:490-498
theorem subst_tt_open_tt_rec (T1 T2 X P : typ) (n : Nat) : type P → subst_tt X P (open_tt_rec n T1 T2) = open_tt_rec n (subst_tt X P T1) (subst_tt X P T2) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:500-507
theorem subst_tt_open_tt (T1 T2 X P : typ) : type P → subst_tt X P (open_tt T1 T2) = open_tt (subst_tt X P T1) (subst_tt X P T2) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:509-517
theorem subst_tt_open_tt_var (X Y : String) (U T : typ) : Y ≠ X → type U → subst_tt X U (open_tt T (var (Nat.ofString Y))) = open_tt (subst_tt X U T) (var (Nat.ofString Y)) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:519-529
theorem subst_tt_intro (X : String) (T2 U : typ) : X ∉ fv_tt T2 → type U → open_tt (subst_tt X U T2) U = T2 := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:531-536
theorem open_te_rec_term_core (e : trm) (j : Nat) (u : trm) (i : Nat) (P : Prop) : term u → term (open_te_rec j u e) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:538-545
theorem open_te_rec_type_core (e : trm) (j : Nat) (Q : typ) (i : Nat) (P : Prop) : i ≠ j → type Q → type (open_te_rec j Q e) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:547-558
theorem open_te_rec_term (e : trm) (U : typ) : term e → type U → term (open_te e U) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:560-566
theorem subst_te_fresh (X : String) (U : typ) (e : trm) : X ∉ fv_te e → subst_te X U e = e := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:568-577
theorem subst_te_open_te (e : trm) (T X : String) (U : typ) : type U → subst_te X U (open_te e (var (Nat.ofString T))) = open_te (subst_te X U e) (subst_tt X U (var (Nat.ofString T))) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:579-587
theorem subst_te_open_te_var (X Y : String) (U : typ) (e : trm) : Y ≠ X → type U → subst_te X U (open_te e (var (Nat.ofString Y))) = open_te (subst_te X U e) (var (Nat.ofString Y)) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:589-599
theorem subst_te_intro (X : String) (U : typ) (e : trm) : X ∉ fv_te e → type U → open_te (subst_te X U e) U = e := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:601-607
theorem open_ee_rec_term_core (e : trm) (j : Nat) (v u : trm) (i : Nat) : i ≠ j → term u → term (open_ee_rec j v e) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:609-614
theorem open_ee_rec_type_core (e : trm) (j : Nat) (V : typ) (u : trm) (i : Nat) : term u → type (open_ee_rec j u e) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:616-626
theorem open_ee_rec_term (u e : trm) : term u → term e → term (open_ee e u) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:628-635
theorem subst_ee_fresh (x : String) (u e : trm) : x ∉ fv_ee e → subst_ee x u e = e := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:637-647
theorem subst_ee_open_ee (t1 t2 u : trm) (x : String) : term u → subst_ee x u (open_ee t1 t2) = open_ee (subst_ee x u t1) (subst_ee x u t2) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:649-657
theorem subst_ee_open_ee_var (x y : String) (u e : trm) : y ≠ x → term u → subst_ee x u (open_ee e (var (Nat.ofString y))) = open_ee (subst_ee x u e) (var (Nat.ofString y)) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:659-668
theorem subst_ee_intro (x : String) (u e : trm) : x ∉ fv_ee e → term u → open_ee (subst_ee x u e) u = e := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:670-678
theorem subst_te_open_ee_var (Z : String) (P : typ) (x : String) (e : trm) : term P → x ≠ Z → subst_te Z P (open_ee e (var (Nat.ofString x))) = open_ee (subst_te Z P e) (var (Nat.ofString x)) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:680-688
theorem subst_ee_open_te_var (z : String) (u : trm) (e : trm) (X : String) : term u → X ∉ fv_te e → subst_ee z u (open_te e (var (Nat.ofString X))) = open_te (subst_ee z u e) (var (Nat.ofString X)) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:690-696
theorem subst_tt_type (T : typ) (Z : String) (P : typ) : type T → type P → type (subst_tt Z P T) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:698-704
theorem subst_te_term (e : trm) (Z : String) (P : typ) : term e → type P → term (subst_te Z P e) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:706-721
theorem subst_ee_term (e1 : trm) (Z : String) (e2 : trm) : term e1 → term e2 → term (subst_ee Z e2 e1) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:723-729
theorem wft_type (E : env) (T : typ) : wft E T → type T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:731-742
theorem wft_weaken (G : env) (T : typ) (E F : env) : wft (E ++ G) T → okt F → wft (E ++ F ++ G) T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:744-754
theorem wft_weaken_empty (T : typ) (F : env) : wft [] T → okt F → wft F T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:756-771
theorem wft_narrow (V0 V1 F U0 U1 T E X : typ) : wft (E ++ (X, bind.sub U0 U1) :: F) V0 → sub E U0 T → sub E T U1 → wft (E ++ (X, bind.sub T T) :: F) V1 := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:773-788
theorem wft_strengthen (E F : env) (x : String) (U T : typ) : wft (E ++ (x, bind.typ U) :: F) T → sub E U T → wft (E ++ F) T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:790-813
theorem wft_subst_tb (F Q0 Q1 E : env) (Z : String) (P T : typ) : wft (E ++ (Z, bind.typ P) :: F) Q0 → wft E P → sub E T P → wft (E ++ F) (subst_tt Z T Q1) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:815-826
theorem wft_subst_tb_empty (F Q0 Q1 Z : String) (P T : typ) : wft ((Z, bind.typ P) :: F) Q0 → wft [] P → sub [] T P → wft F (subst_tt Z T Q1) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:828-845
theorem wft_open (E : env) (U T0 T1 T2 : typ) : wft E U → wft (E ++ ("_", bind.sub U U) :: []) T0 → (∀ X, wft (E ++ (X, bind.sub U U) :: []) T1) → wft E (open_tt T2 T0) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:847-855
theorem ok_from_okt (E : env) : okt E → List.Sorted (· < ·) (E.keys) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:857-874
theorem wft_from_env_has_sub (x : String) (U0 U1 E : env) : List.lookup x E = some (bind.sub U0 U1) → wft E U0 ∧ wft E U1 := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:876-893
theorem wft_from_env_has_typ (x : String) (U E : env) : List.lookup x E = some (bind.typ U) → wft E U := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:895-902
theorem wft_from_okt_typ (x : String) (T : typ) (E : env) : okt E → List.lookup x E = some (bind.typ T) → wft E T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:904-913
theorem wft_from_okt_sub (x : String) (T0 T1 : typ) (E : env) : okt E → List.lookup x E = some (bind.sub T0 T1) → wft E T0 ∧ wft E T1 := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:915-932
theorem wft_weaken_right (T : typ) (E F : env) : wft E T → okt F → wft (E ++ F) T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:934-941
theorem okt_push_inv (E : env) (X : String) (B : bind) : okt ((X, B) :: E) → okt E ∧ X ∉ E.keys := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:943-950
theorem okt_push_sub_inv (E : env) (X : String) (T0 T1 : typ) : okt ((X, bind.sub T0 T1) :: E) → okt E ∧ X ∉ E.keys := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:952-954
theorem okt_push_sub_type (E : env) (X : String) (T0 T1 : typ) : okt ((X, bind.sub T0 T1) :: E) → wft E T0 ∧ wft E T1 := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:956-963
theorem okt_push_typ_inv (E : env) (x : String) (T : typ) : okt ((x, bind.typ T) :: E) → okt E ∧ x ∉ E.keys := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:965-971
theorem okt_push_typ_type (E : env) (X : String) (T : typ) : okt ((X, bind.typ T) :: E) → wft E T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:973-988
theorem okt_narrow (V0 V1 : typ) (E F : env) (U0 U1 X : String) : okt (E ++ (X, bind.sub U0 U1) :: F) → sub E V0 U0 → sub E U1 V1 → okt (E ++ (X, bind.sub V0 V1) :: F) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:990-1004
theorem okt_strengthen (x : String) (T : typ) (E F : env) : okt (E ++ (x, bind.typ T) :: F) → sub E U T → okt (E ++ F) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1006-1020
theorem okt_subst_tb (Q0 Q1 Z : String) (P : typ) (E F : env) : okt (E ++ (Z, bind.typ P) :: F) → wft E P → okt (E ++ F) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1022-1039
theorem okt_subst_tb_empty (Q0 Q1 Z : String) (P : typ) (F : env) : okt ((Z, bind.typ P) :: F) → wft [] P → okt F := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1041-1049
theorem notin_fv_tt_open (Y X : String) (T : typ) : Y ∉ fv_tt T → open_tt T (var (Nat.ofString Y)) = T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1051-1060
theorem notin_fv_wf (E : env) (X : String) (T : typ) : wft E T → X ∉ fv_tt T → wft (E ++ (X, bind.sub T T) :: []) T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1062-1077
theorem map_subst_tb_id (G : env) (Z : String) (P : typ) : (∀ x, List.lookup x G = none) → wft G P → List.map (subst_tb Z P) G = G := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1079-1096
theorem sub_regular (E : env) (S T : typ) : sub E S T → wft E S ∧ wft E T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1098-1139
theorem typing_regular (E : env) (e : trm) (T : typ) : typing E e T → term e ∧ wft E T ∧ okt E := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1141-1147
theorem value_regular (t : trm) : value t → term t := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1149-1199
theorem red_regular (t t' : trm) : red t t' → term t ∧ term t' := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1201-1212
theorem sub_reflexivity (E : env) (T : typ) : wft E T → sub E T T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1214-1228
theorem sub_weakening (E F G : env) (S T : typ) : sub (E ++ G) S T → okt F → sub (E ++ F ++ G) S T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1230-1245
theorem sub_weakening_empty (F G : env) (S T : typ) : sub G S T → okt F → sub (F ++ G) S T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1247-1282
theorem sub_narrowing_aux (Q0 Q1 F E : env) (Z : String) (P0 P1 S T : typ) : (∀ E S T, sub E S T → sub E S T) → wft (E ++ (Z, bind.sub P0 P1) :: F) S → wft (E ++ (Z, bind.sub P0 P1) :: F) T → sub (E ++ (Z, bind.sub S S) :: F) T T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1284-1292
theorem sub_narrowing (Q0 Q1 E F : env) (Z : String) (P0 P1 S T : typ) : sub (E ++ (Z, bind.sub P0 P1) :: F) S T → sub E P0 S → sub E T P1 → sub (E ++ (Z, bind.sub S S) :: F) T T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1294-1310
theorem sub_narrowing_empty (Q0 Q1 Z : String) (P0 P1 S T : typ) : sub ((Z, bind.sub P0 P1) :: []) S T → sub [] P0 S → sub [] T P1 → sub ((Z, bind.sub S S) :: []) T T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1312-1370
theorem sub_through_subst_tt (Q0 Q1 E F : env) (Z S T P : typ) : wft (E ++ (Z, bind.typ P) :: F) S → wft (E ++ (Z, bind.typ P) :: F) T → wft E P → sub (E ++ F) (subst_tt Z P S) (subst_tt Z P T) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1372-1394
theorem typing_weakening (E F G : env) (e : trm) (T : typ) : typing (E ++ G) e T → okt F → typing (E ++ F ++ G) e T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1396-1413
theorem sub_strengthening (x : String) (U E F S T : typ) : sub (E ++ (x, bind.typ U) :: F) S T → sub E U S → sub (E ++ F) S T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1415-1430
theorem typing_narrowing (Q0 Q1 E F : env) (X : String) (P0 P1 e T : typ) : typing (E ++ (X, bind.sub P0 P1) :: F) e T → sub E Q0 P0 → sub E P1 Q1 → typing (E ++ (X, bind.sub Q0 Q1) :: F) e T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1432-1447
theorem typing_narrowing_empty (Q0 Q1 X : String) (P0 P1 e T : typ) : typing ((X, bind.sub P0 P1) :: []) e T → sub [] Q0 P0 → sub [] P1 Q1 → typing ((X, bind.sub Q0 Q1) :: []) e T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1449-1470
theorem typing_through_subst_ee (U E F : env) (x T e u : trm) : typing (E ++ (x, bind.typ U) :: F) e T → typing E u U → typing (E ++ F) (subst_ee x u e) T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1472-1510
theorem typing_through_subst_te (Q0 Q1 E F : env) (Z e T P : typ) : typing (E ++ (Z, bind.typ P) :: F) e T → wft E P → sub E Q0 P → typing (E ++ F) (subst_te Z Q0 e) (subst_tt Z Q1 T) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1512-1525
inductive possible_types : trm → typ → Prop :=
  | pt_var : ∀ x T, possible_types (var x) T

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1527-1538
theorem possible_types_value (p T : typ) : value p → possible_types p T → (∃ U, p = abs T U) ∨ (∃ U, p = tabs T U) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1540-1558
theorem possible_types_closure (v T U : typ) : value v → possible_types v T → sub [] T U → possible_types v U := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1560-1585
theorem possible_types_typing (v T : typ) : value v → typing [] v T → possible_types v T := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1587-1601
theorem typing_inv_abs (S1 e1 T : typ) : typing [] (abs S1 e1) T → ∃ T2, T = arr S1 T2 ∧ (∀ x, typing [(x, bind.typ S1)] e1 T2) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1603-1622
theorem typing_inv_tabs (S10 S11 e1 T : typ) : typing [] (tabs S10 e1) T → ∃ T2, T = all S11 T2 ∧ (∀ X, typing [(X, bind.sub S10 S11)] e1 T2) := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1624-1658
theorem preservation_result : preservation := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1660-1666
theorem value_not_bot (t : trm) (T : typ) : value t → typing [] t T → T ≠ bot := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1668-1676
theorem canonical_form_abs (t U1 U2 : typ) : value t → typing [] t (arr U1 U2) → ∃ e, t = abs U1 e := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1678-1689
theorem canonical_form_tabs (t U0 U1 U2 : typ) : value t → typing [] t (all U0 U1) → ∃ e, t = tabs U0 e := by sorry

-- Coq: Lp2lc_coq\Active\FsubL_alt.v:1691-1691
theorem progress_result : progress := by sorry

namespace Lp2lc.Active.Dsub

-- Coq: Lp2lc_coq\Active\Dsub.v:395-407
theorem open_rec_lc_core (T : typ) (j : Nat) (v u : trm) (i : Nat) (h : i ≠ j) : term u → term (open_t_rec j v T) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:409-416
theorem open_rec_lc (T : typ) : term T → type (open_t T T) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:418-424
theorem open_t_var_type (x : String) (T : typ) : type T → type (open_t (var (Nat.ofString x)) T) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:426-434
theorem subst_fresh (T : typ) (z : String) (u : trm) : z ∉ fv_t T → subst_t z u T = T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:436-445
theorem subst_open_rec (T1 t2 : trm) (x : String) (u : trm) (n : Nat) : term u → subst_t x u (open_t_rec n t2 T1) = open_t_rec n (subst_e x u t2) (subst_t x u T1) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:447-452
theorem subst_t_open_t (T1 t2 : trm) (x : String) (u : trm) : term u → subst_t x u (open_t T1 t2) = open_t (subst_t x u T1) (subst_e x u t2) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:454-461
theorem subst_e_open_e (t1 t2 x : String) (u : trm) : term u → subst_e x u (open_e t1 t2) = open_e (subst_e x u t1) (subst_e x u t2) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:463-468
theorem subst_t_open_t_var (x y : String) (u : trm) (T : typ) : y ≠ x → term u → subst_t x u (open_t T (var (Nat.ofString y))) = open_t (subst_t x u T) (var (Nat.ofString y)) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:470-478
theorem subst_e_open_e_var (x y : String) (u e : trm) : y ≠ x → term u → subst_e x u (open_e e (var (Nat.ofString y))) = open_e (subst_e x u e) (var (Nat.ofString y)) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:480-486
theorem subst_t_intro (x : String) (T2 u : trm) : x ∉ fv_t T2 → term u → open_t (subst_t x u T2) u = T2 := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:488-496
theorem subst_e_intro (x : String) (t2 u : trm) : x ∉ fv_ee t2 → term u → open_e (subst_e x u t2) u = t2 := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:498-506
theorem subst_lc : (∀ (e : trm) (z : String) (u : trm), term e → term u → term (subst_e z u e)) ∧ (∀ (T : typ) (z : String) (u : trm), type T → term u → type (subst_t z u T)) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:508-512
theorem subst_t_type (T : typ) (z : String) (u : trm) : type T → term u → type (subst_t z u T) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:514-518
theorem subst_e_term (e1 : trm) (z : String) (e2 : trm) : term e1 → term e2 → term (subst_e z e2 e1) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:520-534
theorem subst_e_value (e1 : trm) (z : String) (e2 : trm) : value e1 → term e2 → value (subst_e z e2 e1) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:536-546
theorem value_is_term (e : trm) : value e → term e := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:548-553
theorem wf_lc : (∀ (E : env) (T : typ), wft E T → type T) ∧ (∀ (E : env) (e : trm), wfe E e → term e) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:554-558
theorem wft_type (E : env) (T : typ) : wft E T → type T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:560-566
theorem wfe_term (E : env) (e : trm) : wfe E e → term e := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:568-583
theorem wf_weaken : (∀ (G : env) (T : typ) (E F : env), wft (E ++ G) T → okt F → wft (E ++ F ++ G) T) ∧ (∀ (G : env) (T : typ) (E F : env), wfe (E ++ G) T → okt F → wfe (E ++ F ++ G) T) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:585-591
theorem wft_weaken (G : env) (T : typ) (E F : env) : wft (E ++ G) T → okt F → wft (E ++ F ++ G) T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:593-605
theorem wft_weaken_empty (T : typ) (E : env) : wft [] T → okt E → wft E T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:607-613
theorem wfe_weaken (G : env) (T : typ) (E F : env) : wfe (E ++ G) T → okt F → wfe (E ++ F ++ G) T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:615-629
theorem wfe_weaken_empty (T : typ) (E : env) : wfe [] T → okt E → wfe E T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:631-648
theorem wf_narrow : (∀ (E0 : env) (T : typ), wft E0 T → ∀ (V F U E : env) (x : String), wft (E ++ (x, U) :: F) V → sub E U T → wft (E ++ (x, T) :: F) V) ∧ (∀ (E0 : env) (T : typ), wfe E0 T → ∀ (V F U E : env) (x : String), wfe (E ++ (x, U) :: F) V → sub E U T → wfe (E ++ (x, T) :: F) V) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:650-658
theorem wft_narrow (V F U T E : env) (x : String) : wft (E ++ (x, U) :: F) V → sub E U T → wft (E ++ (x, T) :: F) V := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:660-698
theorem wf_subst : (∀ (E0 : env) (T : typ), wft E0 T → ∀ (F Q E : env) (Z : String) (u : trm), wft (E ++ (Z, T) :: F) Q → typing E u T → wft (E ++ F) (subst_t Z u Q)) ∧ (∀ (E0 : env) (T : typ), wfe E0 T → ∀ (F Q E : env) (Z : String) (u : trm), wfe (E ++ (Z, T) :: F) Q → typing E u T → wfe (E ++ F) (subst_e Z u Q)) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:700-707
theorem wft_subst (F Q E : env) (Z : String) (u : trm) (T : typ) : wft (E ++ (Z, T) :: F) Q → typing E u T → wft (E ++ F) (subst_t Z u Q) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:709-720
theorem wft_subst1 (F Q Z : String) (u : trm) (T : typ) : wft ((Z, T) :: F) Q → typing [] u T → wft F (subst_t Z u Q) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:722-736
theorem wft_subst_empty (Q Z : String) (u : trm) (T : typ) : wft ((Z, T) :: []) Q → typing [] u T → wft [] (subst_t Z u Q) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:738-755
theorem wft_open (E : env) (u T1 T2 : typ) : wft E u → wft (E ++ ("_", T1) :: []) T1 → (∀ (x : String), wft (E ++ (x, T1) :: []) T2) → wft E (open_t T2 u) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:757-765
theorem ok_from_okt (E : env) : okt E → List.Sorted (· < ·) (E.keys) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:767-780
theorem wft_from_env_has (x : String) (U E : env) : List.lookup x E = some U → wft E U := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:782-790
theorem wft_from_okt (x : String) (T : typ) (E : env) : okt E → List.lookup x E = some T → wft E T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:792-808
theorem wft_weaken_right (T : typ) (E F : env) : wft E T → okt F → wft (E ++ F) T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:810-816
theorem okt_push_inv (E : env) (x : String) (T : typ) : okt ((x, T) :: E) → okt E ∧ x ∉ E.keys := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:818-830
theorem okt_push_type (E : env) (x : String) (T : typ) : okt ((x, T) :: E) → wft E T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:832-845
theorem okt_narrow (V : typ) (E F : env) (U x : String) : okt (E ++ (x, U) :: F) → sub E U V → okt (E ++ (x, V) :: F) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:847-858
theorem okt_subst (Q Z : String) (u : trm) (E F : env) : okt (E ++ (Z, Q) :: F) → typing E u Q → okt (E ++ F) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:860-881
theorem okt_subst1 (Q Z : String) (u : trm) (F : env) : okt ((Z, Q) :: F) → typing [] u Q → okt F := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:883-891
theorem notin_fv_open_rec : (∀ (T : typ) (k : Nat) (y : String) (x : trm), y ∉ fv_t T → open_t_rec k (var (Nat.ofString y)) T = T) ∧ (∀ (e : trm) (k : Nat) (y : String) (x : trm), y ∉ fv_ee e → open_e_rec k (var (Nat.ofString y)) e = e) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:893-898
theorem notin_fv_t_open (y x : String) (T : typ) : y ∉ fv_t T → open_t T (var (Nat.ofString y)) = T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:900-905
theorem notin_fv_e_open (y x : String) (e : trm) : y ∉ fv_ee e → open_e e (var (Nat.ofString y)) = e := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:907-917
theorem notin_fv_wf_rec : (∀ (E : env) (x : String) (T : typ), wft E T → x ∉ fv_t T) ∧ (∀ (E : env) (x : String) (e : trm), wfe E e → x ∉ fv_ee e) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:919-923
theorem notin_fv_wf (E : env) (x : String) (T : typ) : wft E T → x ∉ fv_t T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:925-937
theorem map_subst_id (G : env) (z : String) (u : trm) : (∀ (x : String), List.lookup x G = none) → wft G (subst_t z u) = G := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:939-951
theorem sub_has_regular : (∀ (E : env) (S T : typ), sub E S T → wft E S ∧ wft E T) ∧ (∀ (E : env) (p T : typ), has E p T → wft E T ∧ wfe E p) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:953-957
theorem sub_regular (E : env) (S T : typ) : sub E S T → wft E S ∧ wft E T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:959-963
theorem has_regular (E : env) (p T : typ) : has E p T → wft E T ∧ wfe E p := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:965-972
theorem has_regular_e (E : env) (p T : typ) : has E p T → term p := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:974-997
theorem typing_regular (E : env) (e : trm) (T : typ) : typing E e T → term e ∧ wft E T ∧ okt E := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:999-1005
theorem value_regular (t : trm) : value t → term t := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1007-1064
theorem red_regular (t t' : trm) : red t t' → term t ∧ term t' := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1066-1078
theorem sub_reflexivity (E : env) (T : typ) : wft E T → sub E T T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1080-1099
theorem sub_has_weakening : (∀ (E0 : env) (S T : typ), sub E0 S T → ∀ (E F G : env), okt F → sub (E ++ F ++ G) S T) ∧ (∀ (E0 : env) (p T : typ), has E0 p T → ∀ (E F G : env), okt F → has (E ++ F ++ G) p T) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1101-1107
theorem sub_weakening (E F G : env) (S T : typ) : sub (E ++ G) S T → okt F → sub (E ++ F ++ G) S T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1109-1122
theorem sub_weakening1 (E F G : env) (S T : typ) : sub (E ++ G) S T → okt F → sub (E ++ F ++ G) S T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1124-1137
theorem sub_weakening_empty (E S T : typ) : sub [] S T → okt E → sub E S T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1139-1145
theorem has_weakening (E F G : env) (p T : typ) : has (E ++ G) p T → okt F → has (E ++ F ++ G) p T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1147-1160
theorem has_weakening1 (E F G : env) (p T : typ) : has (E ++ G) p T → okt F → has (E ++ F ++ G) p T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1162-1182
theorem has_weakening_empty (E p T : typ) : has [] p T → okt E → has E p T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1184-1212
theorem sub_has_narrowing_aux : (∀ (Q : env → typ → typ → Prop) (F E : env) (Z : String) (P S T : typ), (∀ (E : env) (S T : typ), sub E S T → Q E S T) → wft (E ++ (Z, P) :: F) S → wft (E ++ (Z, P) :: F) T → Q (E ++ (Z, S) :: F) T) ∧ (∀ (Q : env → trm → typ → Prop) (F E : env) (Z : String) (P e T : typ), (∀ (E : env) (p T : typ), has E p T → Q E p T) → wfe (E ++ (Z, P) :: F) e → wft (E ++ (Z, P) :: F) T → Q (E ++ (Z, e) :: F) T) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1214-1221
theorem sub_narrowing (Q E F : env) (Z : String) (P S T : typ) : sub (E ++ (Z, P) :: F) S T → sub E P S → sub (E ++ (Z, S) :: F) T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1223-1238
theorem sub_narrowing_empty (Q Z : String) (P S T : typ) : sub ((Z, P) :: []) S T → sub [] P S → sub ((Z, S) :: []) T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1240-1248
theorem has_value_var (E : env) (u : trm) (T : typ) : value u → typing E u T → has E u T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1250-1258
theorem var_typing_has (E : env) (x : String) (Q : typ) : typing E (var (Nat.ofString x)) Q → has E (var (Nat.ofString x)) Q := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1260-1271
theorem val_typing_has (E : env) (u : trm) (Q : typ) : value u → typing E u Q → has E u Q := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1273-1332
theorem sub_has_through_subst : (∀ (E0 : env) (S T : typ), sub E0 S T → ∀ (Q E F : env) (Z : String) (u : trm), wft (E ++ (Z, S) :: F) T → typing E u S → wft (E ++ F) (subst_t Z u T)) ∧ (∀ (E0 : env) (p T : typ), has E0 p T → ∀ (Q E F : env) (Z : String) (u : trm), wft (E ++ (Z, p) :: F) T → typing E u p → wft (E ++ F) (subst_t Z u T)) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1334-1350
theorem typing_weakening (E F G : env) (e : trm) (T : typ) : typing (E ++ G) e T → okt F → typing (E ++ F ++ G) e T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1352-1368
theorem typing_narrowing (Q E F : env) (X : String) (P e T : typ) : typing (E ++ (X, P) :: F) e T → sub E Q P → typing (E ++ (X, Q) :: F) e T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1370-1383
theorem typing_narrowing_empty (Q X : String) (P e T : typ) : typing ((X, P) :: []) e T → sub [] Q P → typing ((X, Q) :: []) e T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1385-1421
theorem typing_through_subst (U E F : env) (z T e u : trm) : typing (E ++ (z, U) :: F) e T → typing E u U → typing (E ++ F) (subst_e z u e) (subst_t z u T) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1423-1451
inductive psub : typ → typ → Prop :=
  | psub_refl : ∀ T, psub T T
  | psub_trans : ∀ S T U, psub S T → psub T U → psub S U
  | psub_arr : ∀ S1 S2 T1 T2, psub S1 T1 → psub T2 S2 → psub (arr S1 S2) (arr T1 T2)
  | psub_all : ∀ e S T, psub S T → psub (all e S) (all e T)

-- Coq: Lp2lc_coq\Active\Dsub.v:1453-1463
theorem has_empty_value (p T : typ) : has [] p T → value p := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1465-1476
theorem psub_sub (S T : typ) : psub S T → sub [] S T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1478-1493
inductive possible_types : Nat → trm → typ → Prop :=
  | pt_var : ∀ n x T, possible_types n (var x) T

-- Coq: Lp2lc_coq\Active\Dsub.v:1495-1508
theorem possible_types_value (n : Nat) (p T : typ) : value p → possible_types n p T → (∃ U, p = abs T U) ∨ (∃ U, p = tabs T U) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1510-1522
theorem possible_types_wfe (n : Nat) (p T : typ) : possible_types n p T → wfe [] p := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1524-1537
theorem possible_types_wft (n : Nat) (p T : typ) : possible_types n p T → wft [] T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1539-1550
theorem has_empty_var_false (x T : typ) : has [] (var (Nat.ofString x)) T → False := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1552-1573
theorem possible_types_closure_psub (n : Nat) (v T U : typ) : value v → possible_types n v T → psub T U → possible_types n v U := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1575-1588
theorem psub_reflexivity (T : typ) : psub T T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1590-1610
theorem sub_psub_aux : psub S T → sub E S T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1612-1616
theorem sub_psub (S T : typ) : sub [] S T → psub S T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1618-1625
theorem possible_types_closure (n : Nat) (v T U : typ) : value v → possible_types n v T → sub [] T U → possible_types n v U := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1627-1646
theorem possible_types_typing (v T : typ) : value v → typing [] v T → possible_types 0 v T := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1648-1665
theorem typing_inv_abs (S1 e1 T : typ) : typing [] (abs S1 e1) T → ∃ T2, T = arr S1 T2 ∧ (∀ x, typing [(x, S1)] e1 T2) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1667-1674
theorem canonical_form_abs (t U1 U2 : typ) : value t → typing [] t (arr U1 U2) → ∃ e, t = abs U1 e := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1676-1683
theorem canonical_form_mem (t b T : typ) : value t → typing [] t (all b T) → False := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1685-1700
theorem typing_through_subst1 (V y v e T : typ) : typing [(y, V)] e T → typing [] v V → typing [] (subst_e y v e) (subst_t y v T) := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1702-1706
theorem value_red_contra (e e' : trm) : value e → red e e' → False := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1708-1749
theorem preservation_result : preservation := by sorry

-- Coq: Lp2lc_coq\Active\Dsub.v:1751-1751
theorem progress_result : progress := by sorry

namespace Lp2lc.Active.Dsubsup

-- Coq: Lp2lc_coq\Active\Dsubsup.v:406-418
theorem open_rec_lc_core (T : typ) (j : Nat) (v u : trm) (i : Nat) (h : i ≠ j) : term u → term (open_t_rec j v T) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:420-427
theorem open_rec_lc (T : typ) : term T → type (open_t T T) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:429-435
theorem open_t_var_type (x : String) (T : typ) : type T → type (open_t (var (Nat.ofString x)) T) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:437-445
theorem subst_fresh (T : typ) (z : String) (u : trm) : z ∉ fv_t T → subst_t z u T = T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:447-456
theorem subst_open_rec (T1 t2 : trm) (x : String) (u : trm) (n : Nat) : term u → subst_t x u (open_t_rec n t2 T1) = open_t_rec n (subst_e x u t2) (subst_t x u T1) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:458-463
theorem subst_t_open_t (T1 t2 : trm) (x : String) (u : trm) : term u → subst_t x u (open_t T1 t2) = open_t (subst_t x u T1) (subst_e x u t2) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:465-472
theorem subst_e_open_e (t1 t2 x : String) (u : trm) : term u → subst_e x u (open_e t1 t2) = open_e (subst_e x u t1) (subst_e x u t2) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:474-479
theorem subst_t_open_t_var (x y : String) (u : trm) (T : typ) : y ≠ x → term u → subst_t x u (open_t T (var (Nat.ofString y))) = open_t (subst_t x u T) (var (Nat.ofString y)) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:481-489
theorem subst_e_open_e_var (x y : String) (u e : trm) : y ≠ x → term u → subst_e x u (open_e e (var (Nat.ofString y))) = open_e (subst_e x u e) (var (Nat.ofString y)) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:491-497
theorem subst_t_intro (x : String) (T2 u : trm) : x ∉ fv_t T2 → term u → open_t (subst_t x u T2) u = T2 := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:499-507
theorem subst_e_intro (x : String) (t2 u : trm) : x ∉ fv_ee t2 → term u → open_e (subst_e x u t2) u = t2 := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:509-517
theorem subst_lc : (∀ (e : trm) (z : String) (u : trm), term e → term u → term (subst_e z u e)) ∧ (∀ (T : typ) (z : String) (u : trm), type T → term u → type (subst_t z u T)) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:519-523
theorem subst_t_type (T : typ) (z : String) (u : trm) : type T → term u → type (subst_t z u T) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:525-529
theorem subst_e_term (e1 : trm) (z : String) (e2 : trm) : term e1 → term e2 → term (subst_e z e2 e1) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:531-545
theorem subst_e_value (e1 : trm) (z : String) (e2 : trm) : value e1 → term e2 → value (subst_e z e2 e1) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:547-557
theorem value_is_term (e : trm) : value e → term e := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:559-564
theorem wf_lc : (∀ (E : env) (T : typ), wft E T → type T) ∧ (∀ (E : env) (e : trm), wfe E e → term e) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:565-569
theorem wft_type (E : env) (T : typ) : wft E T → type T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:571-577
theorem wfe_term (E : env) (e : trm) : wfe E e → term e := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:579-594
theorem wf_weaken : (∀ (G : env) (T : typ) (E F : env), wft (E ++ G) T → okt F → wft (E ++ F ++ G) T) ∧ (∀ (G : env) (T : typ) (E F : env), wfe (E ++ G) T → okt F → wfe (E ++ F ++ G) T) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:596-602
theorem wft_weaken (G : env) (T : typ) (E F : env) : wft (E ++ G) T → okt F → wft (E ++ F ++ G) T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:604-616
theorem wft_weaken_empty (T : typ) (E : env) : wft [] T → okt E → wft E T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:618-624
theorem wfe_weaken (G : env) (T : typ) (E F : env) : wfe (E ++ G) T → okt F → wfe (E ++ F ++ G) T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:626-640
theorem wfe_weaken_empty (T : typ) (E : env) : wfe [] T → okt E → wfe E T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:642-660
theorem wf_narrow : (∀ (E0 : env) (T : typ), wft E0 T → ∀ (V F U E : env) (x : String), wft (E ++ (x, U) :: F) V → sub E U T → wft (E ++ (x, T) :: F) V) ∧ (∀ (E0 : env) (T : typ), wfe E0 T → ∀ (V F U E : env) (x : String), wfe (E ++ (x, U) :: F) V → sub E U T → wfe (E ++ (x, T) :: F) V) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:662-670
theorem wft_narrow (V F U T E : env) (x : String) : wft (E ++ (x, U) :: F) V → sub E U T → wft (E ++ (x, T) :: F) V := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:672-706
theorem wf_subst : (∀ (E0 : env) (T : typ), wft E0 T → ∀ (F Q E : env) (Z : String) (u : trm), wft (E ++ (Z, T) :: F) Q → typing E u T → wft (E ++ F) (subst_t Z u Q)) ∧ (∀ (E0 : env) (T : typ), wfe E0 T → ∀ (F Q E : env) (Z : String) (u : trm), wfe (E ++ (Z, T) :: F) Q → typing E u T → wfe (E ++ F) (subst_e Z u Q)) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:708-715
theorem wft_subst (F Q E : env) (Z : String) (u : trm) (T : typ) : wft (E ++ (Z, T) :: F) Q → typing E u T → wft (E ++ F) (subst_t Z u Q) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:717-728
theorem wft_subst1 (F Q Z : String) (u : trm) (T : typ) : wft ((Z, T) :: F) Q → typing [] u T → wft F (subst_t Z u Q) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:730-744
theorem wft_subst_empty (Q Z : String) (u : trm) (T : typ) : wft ((Z, T) :: []) Q → typing [] u T → wft [] (subst_t Z u Q) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:746-763
theorem wft_open (E : env) (u T1 T2 : typ) : wft E u → wft (E ++ ("_", T1) :: []) T1 → (∀ (x : String), wft (E ++ (x, T1) :: []) T2) → wft E (open_t T2 u) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:765-773
theorem ok_from_okt (E : env) : okt E → List.Sorted (· < ·) (E.keys) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:775-788
theorem wft_from_env_has (x : String) (U E : env) : List.lookup x E = some U → wft E U := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:790-798
theorem wft_from_okt (x : String) (T : typ) (E : env) : okt E → List.lookup x E = some T → wft E T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:800-816
theorem wft_weaken_right (T : typ) (E F : env) : wft E T → okt F → wft (E ++ F) T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:818-824
theorem okt_push_inv (E : env) (x : String) (T : typ) : okt ((x, T) :: E) → okt E ∧ x ∉ E.keys := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:826-836
theorem okt_push_type (E : env) (x : String) (T : typ) : okt ((x, T) :: E) → wft E T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:838-850
theorem okt_narrow (V : typ) (E F : env) (U x : String) : okt (E ++ (x, U) :: F) → sub E U V → okt (E ++ (x, V) :: F) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:852-894
theorem okt_subst (Q Z : String) (u : trm) (E F : env) : okt (E ++ (Z, Q) :: F) → typing E u Q → okt (E ++ F) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:896-917
theorem okt_subst1 (Q Z : String) (u : trm) (F : env) : okt ((Z, Q) :: F) → typing [] u Q → okt F := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:919-927
theorem notin_fv_open_rec : (∀ (T : typ) (k : Nat) (y : String) (x : trm), y ∉ fv_t T → open_t_rec k (var (Nat.ofString y)) T = T) ∧ (∀ (e : trm) (k : Nat) (y : String) (x : trm), y ∉ fv_ee e → open_e_rec k (var (Nat.ofString y)) e = e) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:929-934
theorem notin_fv_t_open (y x : String) (T : typ) : y ∉ fv_t T → open_t T (var (Nat.ofString y)) = T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:936-941
theorem notin_fv_e_open (y x : String) (e : trm) : y ∉ fv_ee e → open_e e (var (Nat.ofString y)) = e := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:943-953
theorem notin_fv_wf_rec : (∀ (E : env) (x : String) (T : typ), wft E T → x ∉ fv_t T) ∧ (∀ (E : env) (x : String) (e : trm), wfe E e → x ∉ fv_ee e) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:955-959
theorem notin_fv_wf (E : env) (x : String) (T : typ) : wft E T → x ∉ fv_t T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:961-973
theorem map_subst_id (G : env) (z : String) (u : trm) : (∀ (x : String), List.lookup x G = none) → wft G (subst_t z u) = G := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:975-987
theorem sub_has_regular : (∀ (E : env) (S T : typ), sub E S T → wft E S ∧ wft E T) ∧ (∀ (E : env) (p T : typ), has E p T → wft E T ∧ wfe E p) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:989-993
theorem sub_regular (E : env) (S T : typ) : sub E S T → wft E S ∧ wft E T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:995-999
theorem has_regular (E : env) (p T : typ) : has E p T → wft E T ∧ wfe E p := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1001-1008
theorem has_regular_e (E : env) (p T : typ) : has E p T → term p := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1010-1033
theorem typing_regular (E : env) (e : trm) (T : typ) : typing E e T → term e ∧ wft E T ∧ okt E := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1035-1041
theorem value_regular (t : trm) : value t → term t := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1043-1100
theorem red_regular (t t' : trm) : red t t' → term t ∧ term t' := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1102-1114
theorem sub_reflexivity (E : env) (T : typ) : wft E T → sub E T T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1116-1134
theorem sub_has_weakening : (∀ (E0 : env) (S T : typ), sub E0 S T → ∀ (E F G : env), okt F → sub (E ++ F ++ G) S T) ∧ (∀ (E0 : env) (p T : typ), has E0 p T → ∀ (E F G : env), okt F → has (E ++ F ++ G) p T) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1136-1142
theorem sub_weakening (E F G : env) (S T : typ) : sub (E ++ G) S T → okt F → sub (E ++ F ++ G) S T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1144-1157
theorem sub_weakening1 (E F G : env) (S T : typ) : sub (E ++ G) S T → okt F → sub (E ++ F ++ G) S T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1159-1172
theorem sub_weakening_empty (E S T : typ) : sub [] S T → okt E → sub E S T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1174-1180
theorem has_weakening (E F G : env) (p T : typ) : has (E ++ G) p T → okt F → has (E ++ F ++ G) p T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1182-1195
theorem has_weakening1 (E F G : env) (p T : typ) : has (E ++ G) p T → okt F → has (E ++ F ++ G) p T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1197-1217
theorem has_weakening_empty (E p T : typ) : has [] p T → okt E → has E p T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1219-1248
theorem sub_has_narrowing_aux : (∀ (Q : env → typ → typ → Prop) (F E : env) (Z : String) (P S T : typ), (∀ (E : env) (S T : typ), sub E S T → Q E S T) → wft (E ++ (Z, P) :: F) S → wft (E ++ (Z, P) :: F) T → Q (E ++ (Z, S) :: F) T) ∧ (∀ (Q : env → trm → typ → Prop) (F E : env) (Z : String) (P e T : typ), (∀ (E : env) (p T : typ), has E p T → Q E p T) → wfe (E ++ (Z, P) :: F) e → wft (E ++ (Z, P) :: F) T → Q (E ++ (Z, e) :: F) T) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1250-1257
theorem sub_narrowing (Q E F : env) (Z : String) (P S T : typ) : sub (E ++ (Z, P) :: F) S T → sub E P S → sub (E ++ (Z, S) :: F) T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1259-1274
theorem sub_narrowing_empty (Q Z : String) (P S T : typ) : sub ((Z, P) :: []) S T → sub [] P S → sub ((Z, S) :: []) T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1276-1284
theorem has_value_var (E : env) (u : trm) (T : typ) : value u → typing E u T → has E u T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1286-1294
theorem var_typing_has (E : env) (x : String) (Q : typ) : typing E (var (Nat.ofString x)) Q → has E (var (Nat.ofString x)) Q := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1296-1307
theorem val_typing_has (E : env) (u : trm) (Q : typ) : value u → typing E u Q → has E u Q := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1309-1368
theorem sub_has_through_subst : (∀ (E0 : env) (S T : typ), sub E0 S T → ∀ (Q E F : env) (Z : String) (u : trm), wft (E ++ (Z, S) :: F) T → typing E u S → wft (E ++ F) (subst_t Z u T)) ∧ (∀ (E0 : env) (p T : typ), has E0 p T → ∀ (Q E F : env) (Z : String) (u : trm), wft (E ++ (Z, p) :: F) T → typing E u p → wft (E ++ F) (subst_t Z u T)) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1370-1386
theorem typing_weakening (E F G : env) (e : trm) (T : typ) : typing (E ++ G) e T → okt F → typing (E ++ F ++ G) e T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1388-1404
theorem typing_narrowing (Q E F : env) (X : String) (P e T : typ) : typing (E ++ (X, P) :: F) e T → sub E Q P → typing (E ++ (X, Q) :: F) e T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1406-1419
theorem typing_narrowing_empty (Q X : String) (P e T : typ) : typing ((X, P) :: []) e T → sub [] Q P → typing ((X, Q) :: []) e T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1421-1457
theorem typing_through_subst (U E F : env) (z T e u : trm) : typing (E ++ (z, U) :: F) e T → typing E u U → typing (E ++ F) (subst_e z u e) (subst_t z u T) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1459-1487
inductive psub : typ → typ → Prop :=
  | psub_refl : ∀ T, psub T T
  | psub_trans : ∀ S T U, psub S T → psub T U → psub S U
  | psub_arr : ∀ S1 S2 T1 T2, psub S1 T1 → psub T2 S2 → psub (arr S1 S2) (arr T1 T2)
  | psub_all : ∀ e S T, psub S T → psub (all e S) (all e T)

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1489-1499
theorem has_empty_value (p T : typ) : has [] p T → value p := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1501-1511
theorem psub_sub (S T : typ) : psub S T → sub [] S T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1513-1527
inductive possible_types : Nat → trm → typ → Prop :=
  | pt_var : ∀ n x T, possible_types n (var x) T

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1529-1541
theorem possible_types_value (n : Nat) (p T : typ) : value p → possible_types n p T → (∃ U, p = abs T U) ∨ (∃ U, p = tabs T U) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1543-1554
theorem possible_types_wfe (n : Nat) (p T : typ) : possible_types n p T → wfe [] p := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1556-1568
theorem possible_types_wft (n : Nat) (p T : typ) : possible_types n p T → wft [] T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1570-1581
theorem has_empty_var_false (x T : typ) : has [] (var (Nat.ofString x)) T → False := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1583-1603
theorem possible_types_closure_psub (n : Nat) (v T U : typ) : value v → possible_types n v T → psub T U → possible_types n v U := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1605-1615
theorem psub_reflexivity (T : typ) : psub T T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1617-1637
theorem sub_psub_aux : psub S T → sub E S T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1639-1643
theorem sub_psub (S T : typ) : sub [] S T → psub S T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1645-1652
theorem possible_types_closure (n : Nat) (v T U : typ) : value v → possible_types n v T → sub [] T U → possible_types n v U := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1654-1673
theorem possible_types_typing (v T : typ) : value v → typing [] v T → possible_types 0 v T := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1675-1692
theorem typing_inv_abs (S1 e1 T : typ) : typing [] (abs S1 e1) T → ∃ T2, T = arr S1 T2 ∧ (∀ x, typing [(x, S1)] e1 T2) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1694-1701
theorem canonical_form_abs (t U1 U2 : typ) : value t → typing [] t (arr U1 U2) → ∃ e, t = abs U1 e := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1703-1710
theorem canonical_form_mem (t b T : typ) : value t → typing [] t (all b T) → False := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1712-1727
theorem typing_through_subst1 (V y v e T : typ) : typing [(y, V)] e T → typing [] v V → typing [] (subst_e y v e) (subst_t y v T) := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1729-1733
theorem value_red_contra (e e' : trm) : value e → red e e' → False := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1735-1776
theorem preservation_result : preservation := by sorry

-- Coq: Lp2lc_coq\Active\Dsubsup.v:1778-1778
theorem progress_result : progress := by sorry

import Lp2lc.Active.Fsub.Def
import Lp2lc.Active.FsubL_alt.Def
import Lp2lc.Active.Dsub.Def
import Lp2lc.Active.Dsubsup.Def
import Lp2lc.Active.Ddia.Def

set_option autoImplicit true

open scoped Classical
