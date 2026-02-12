import MiniKernel.Kernel

def Level.eval (l : Level) (ctx : Name → Nat) : Nat :=
  match l with
  | .zero => 0
  | .succ l' => l'.eval ctx + 1
  | .max l1 l2 => Nat.max (l1.eval ctx) (l2.eval ctx)
  | .imax l1 l2 => if (l2.eval ctx) = 0 then 0 else Nat.max (l1.eval ctx) (l2.eval ctx)
  | .param n => ctx n

@[grind] inductive Level.NF : Level → Prop
  | zero : Level.NF .zero
  | succ : Level.NF l → Level.NF (.succ l)
  | max : Level.NF l1 → Level.NF l2 → Level.NF (.max l1 l2)
  | imax : Level.NF l1 → Level.NF (.imax l1 (.param u))
  | param : Level.NF (.param n)

@[grind .] theorem Level.NF.mkIMax (h1 : Level.NF l1) (h2 : Level.NF l2) : Level.NF (.mkIMax l1 l2) := by
  fun_induction Level.mkIMax <;> grind

@[grind .] theorem Level.NF.simplify : Level.NF (simplify l) := by
  fun_induction Level.simplify <;> grind

@[grind =] theorem Level.mkIMax_correct (ctx : Name → Nat) (l1 l2 : Level): (mkIMax l1 l2).eval ctx = (Level.imax l1 l2).eval ctx := by
  fun_induction mkIMax<;> try grind [Level.eval]

@[simp] theorem Level.elimIMax_correct (ctx : Name → Nat) (l : Level): l.elimIMax.eval ctx = l.eval ctx := by
  fun_induction Level.elimIMax <;> grind [Level.eval]

@[simp] theorem Level.simplify_correct (ctx : Name → Nat) (l : Level): l.simplify.eval ctx = l.eval ctx := by
  fun_induction Level.simplify <;> grind [Level.eval]

theorem Level.substOneLevel_eval' {ctx ctx' p} (l1 l2 : Level)
  (h : l2.eval ctx' = ctx p)
  (h2 : ∀ p', p ≠ p' → ctx' p' = ctx p') :
  (l1.substOneLevel p l2).eval ctx' = l1.eval ctx := by
  unfold substOneLevel
  fun_induction substLevel <;> grind [Level.eval]

theorem Level.substOneLevel_eval (l1 l2 : Level) (h : l2.eval ctx = ctx p):
  (l1.substOneLevel p l2).eval ctx = l1.eval ctx :=
  Level.substOneLevel_eval' _ _ h (by grind)

theorem Level.le_correct (ctx : Name → Nat) (l1 l2 : Level) balance : l1.le l2 balance = true → l1.eval ctx ≤ l2.eval ctx + balance := by
  fun_induction Level.le l1 l2 balance generalizing ctx <;> try grind [Level.eval]
  case case5 l2 balance l1 p _ ih =>
    match h : ctx p with
    | .zero =>
      unfold byCases
      specialize ih ((l1.imax (param p)).substOneLevel p .zero).elimIMax
                    (l2.substOneLevel p .zero).elimIMax
                    (fun _ => by grind [countIMax, elimIMax])
                    ctx
      simp [elimIMax] at ih
      intro hle
      specialize ih (by simp [elimIMax] at hle; grind)
      simp [eval] at ih
      rw [Level.substOneLevel_eval] at ih
      case h => simp [h, eval]
      simp [eval, h]
      assumption
    | .succ n =>
      unfold byCases
      specialize ih ((l1.imax (param p)).substOneLevel p ((Level.param p).succ)).elimIMax
                    (l2.substOneLevel p ((Level.param p).succ)).elimIMax
                    (fun _ => by grind [countIMax, elimIMax])
                    (fun p' => if p' = p then n else ctx p')
      simp [elimIMax] at ih
      intro hle
      specialize ih (by simp [elimIMax] at hle; grind)
      simp [eval] at ih
      rw [Level.substOneLevel_eval' (ctx := ctx)] at ih
      case h => simp [h, eval]
      case h2 => grind
      rw [Level.substOneLevel_eval' (ctx := ctx)] at ih
      case h => simp [h, eval]
      case h2 => grind
      simp [eval, h]
      assumption
  case case6 l1 balance l2 p _ _ _ ih =>
    match h : ctx p with
    | .zero =>
      unfold byCases
      specialize ih (l1.substOneLevel p .zero).elimIMax
                    ((l2.imax (param p)).substOneLevel p .zero).elimIMax
                    (fun _ => by grind [countIMax, elimIMax])
                    ctx
      simp [elimIMax] at ih
      intro hle
      specialize ih (by simp [elimIMax] at hle; grind)
      simp [eval] at ih
      rw [Level.substOneLevel_eval] at ih
      case h => simp [h, eval]
      simp [eval, h]
      assumption
    | .succ n =>
      unfold byCases
      specialize ih (l1.substOneLevel p ((Level.param p).succ)).elimIMax
                   ((l2.imax (param p)).substOneLevel p ((Level.param p).succ)).elimIMax
                    (fun _ => by grind [countIMax, elimIMax])
                    (fun p' => if p' = p then n else ctx p')
      simp [elimIMax] at ih
      intro hle
      specialize ih (by simp [elimIMax] at hle; grind)
      simp [eval] at ih
      rw [Level.substOneLevel_eval' (ctx := ctx)] at ih
      case h => simp [h, eval]
      case h2 => grind
      rw [Level.substOneLevel_eval' (ctx := ctx)] at ih
      case h => simp [h, eval]
      case h2 => grind
      simp [eval, h]
      assumption

theorem Level.le_complete (ctx : Name → Nat) (l1 l2 : Level) (balance : Int) :
    (∀ ctx, l1.eval ctx ≤ l2.eval ctx + balance) → l1.le l2 balance = true := by
  intro hle
  fun_induction Level.le l1 l2 balance <;> try grind [Level.eval]
  case case4 balance p1 p2 => -- param case
    by_cases p2 = p1
    · subst p2
      specialize hle (fun _ => 0)
      simp_all [eval]
    · exfalso
      specialize hle (fun p' => if p' = p1 then Int.natAbs balance + 1 else 0)
      grind [eval]
  case case5 => -- byCases case
    sorry
  case case6 => -- byCases case 2
    sorry
  case case7 => -- unreachable case due to NF
    sorry
  case case8 => -- unreachable case due to NF
    sorry
  case case9 => -- param le max
    simp only [Bool.or_eq_true]
    simp [eval] at *
    sorry
  case case10 => -- zero le max
    simp only [Bool.or_eq_true]
    simp [eval] at *
    sorry
  case case12 =>
    simp_all [eval]
    specialize hle (fun _ => 0)
    grind
  case case13 =>
    simp_all [eval]
    specialize hle (fun _ => 0)
    grind
  case case14 balance _ _ =>
    simp_all [eval]
    specialize hle (fun _ => Int.natAbs balance + 1)
    grind
