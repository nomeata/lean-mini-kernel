import MiniKernel.Kernel

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


def Level.eval (l : Level) (ctx : Name → Nat) : Nat :=
  match l with
  | .zero => 0
  | .succ l' => l'.eval ctx + 1
  | .max l1 l2 => Nat.max (l1.eval ctx) (l2.eval ctx)
  | .imax l1 l2 => if (l2.eval ctx) = 0 then 0 else Nat.max (l1.eval ctx) (l2.eval ctx)
  | .param n => ctx n

theorem Level.eval_mono (ctx1 ctx2 : Name → Nat) (l : Level)
  (hmono : ∀ n, ctx1 n ≤ ctx2 n) : l.eval ctx1 ≤ l.eval ctx2 := by
  fun_induction Level.eval l ctx1 <;> grind [eval]

theorem Level.forall_zero_le_eval (balance : Int) (l : Level) :
  (∀ ctx, 0 ≤ l.eval ctx + balance) ↔ 0 ≤ l.eval (fun _ => 0) + balance:= by
  constructor
  · intro h; apply h
  · intro h0 ctx
    have := Level.eval_mono (fun _ => 0) ctx l (by grind)
    grind

def Option.imax (o1 o2 : Option Nat) : Option Nat :=
  match o1, o2 with
  | none, none => none
  | _, none => none
  | none, some n => some n
  | some n1, some n2 => some (Nat.max n1 n2)

def Level.coeff (l : Level) (p : Name) : Option Nat :=
  match l with
  | .zero => none
  | .succ l' => .succ <$> coeff l' p
  | .max l1 l2 => Max.max (coeff l1 p) (coeff l2 p)
  | .imax l1 (.param n) => if n = p then Max.max (coeff l1 p) (some 0) else none
  | .imax _ _ => none -- unreachable due to NF
  | .param n => if n = p then some 0 else none

theorem Level.coeff_le_eval_none (n : Nat) (l : Level) (p : Name)
  (hwf : l.NF) (h : l.coeff p = none) : l.eval (fun p' => if p' = p then n else 0) = l.eval (fun _ => 0) := by
  induction hwf generalizing n <;> simp_all only [coeff] <;> simp_all [eval]

theorem Level.coeff_some_eval (l : Level) (p : Name) (hwf : l.NF) (h : l.coeff p = some c) :
    ∃ n, ∀ m > n, l.eval (fun p' => if p' = p then m else 0) = c + m := by
  induction hwf generalizing c <;> simp_all only [coeff, eval] <;> try grind [coeff, eval, Functor.map]
  case succ l hwf ih =>
    revert ih h; cases l.coeff p <;> intro ih h
    · contradiction
    · simp at h; subst c
      obtain ⟨n, ih⟩ := ih rfl
      exists n
      intro m hm
      grind
  case max l1 l2 hwf1 hwf2 ih1 ih2 =>
    revert ih1 ih2 h; cases hc1 : l1.coeff p <;> cases hc2 : l2.coeff p <;> intro ih1 ih2 h <;> simp at h
    · subst c
      clear ih1
      obtain ⟨n2, ih2⟩ := ih2 rfl
      exists Max.max (l1.eval (fun _ => 0)) n2
      intro m hm
      rw [Level.coeff_le_eval_none _ l1 p hwf1 hc1]
      specialize ih2 m (by grind)
      grind
    · subst c
      clear ih2
      obtain ⟨n1, ih1⟩ := ih1 rfl
      exists Max.max n1 (l2.eval (fun _ => 0))
      intro m hm
      rw [Level.coeff_le_eval_none _ l2 p hwf2 hc2]
      specialize ih1 m (by grind)
      grind
    · subst c
      obtain ⟨n1, ih1⟩ := ih1 rfl
      obtain ⟨n2, ih2⟩ := ih2 rfl
      exists Max.max n1 n2
      intro m hm
      specialize ih1 m (by grind)
      specialize ih2 m (by grind)
      grind
  case imax l1 p' hwf1 ih1 =>
    by_cases hp : p' = p
    · simp [hp] at *
      skip
      revert ih1 h; cases h1 : l1.coeff p <;> intro ih1 h <;> simp at h <;> subst h
      case pos.none =>
        exists l1.eval (fun _ => 0)
        intro m hm
        rw [Level.coeff_le_eval_none _ l1 p hwf1 h1]
        grind
      case pos.some c =>
        simp_all
        obtain ⟨n1, ih1⟩ := ih1
        exists n1
        intro m hm
        specialize ih1 m (by grind)
        grind
    · simp [hp] at *
  case param n =>
    simp at h
    exists 0
    grind

theorem Level.coeff_le_eval_some (l : Level) (p : Name) (ctx : Name → Nat)
  (hwf : l.NF) (h : l.coeff p = some n) (hp : 0 < ctx p) : n + ctx p ≤ l.eval ctx := by
  induction hwf generalizing n <;> simp_all only [coeff] <;> try grind [coeff, eval, Functor.map]
  case succ =>
    simp_all [Functor.map, eval]; grind
  case max l1 l2 hl1 hl2 ih1 ih2 =>
    simp_all [eval]
    revert ih1 ih2 h
    cases l1.coeff p <;> cases l2.coeff p <;> grind
  case imax l1 p' hl1 ih1 =>
    simp_all [eval]
    revert ih1 h
    cases l1.coeff p <;> by_cases p' = p <;> grind

theorem Level.forall_param_le_eval (balance : Int) (l : Level) (p : Name) (hwf : l.NF) :
  (∀ ctx, ctx p ≤ l.eval ctx + balance) ↔
  (0 ≤ l.eval (fun _ => 0) + balance ∧ ∃ n, l.coeff p = some n ∧ 0 ≤ n + balance) := by
  cases h : l.coeff p
  case none =>
    constructor
    · intro h
      exfalso
      specialize h (fun p' => if p' = p then Int.natAbs balance + l.eval (fun _ => 0) + 1 else 0)
      have := Level.coeff_le_eval_none (Int.natAbs balance + l.eval (fun _ => 0) + 1) l p hwf ‹_›
      simp_all
      grind
    · simp
  case some n =>
    constructor
    · intro h
      constructor
      · apply h
      · simp
        obtain ⟨k, hk⟩ := Level.coeff_some_eval l p hwf ‹_›
        specialize hk (k+1) (by grind)
        specialize h (fun p' => if p' = p then k + 1 else 0)
        rw [hk] at h; clear hk
        grind
    · intro ⟨h1,h2⟩ ctx
      by_cases h0 : ctx p = 0
      · simp [h0] at *
        have := Level.eval_mono (fun _ => 0) ctx l (by grind)
        grind
      · have := Level.coeff_le_eval_some l p ctx hwf ‹_›
        obtain ⟨_, heq, h2⟩ := h2
        simp at heq; subst heq
        grind

theorem counter_example (p : Name) :
  let l1 := Level.zero.succ
  let l2 := .imax ((Level.param p).succ) (.param p)
  let balance : Int := -1
  let ctx1 := fun n => if n = p then 2 else 0
  let ctx2 := fun n => if n = p then 0 else 0
  (l1.NF) ∧ (l2.NF) ∧
  (∀ ctx, ctx p ≤ (l1.max l2).eval ctx + balance) ∧
  (¬ ctx1 p ≤ l1.eval ctx1 + balance) ∧ (¬ ctx2 p ≤ l2.eval ctx2 + balance) := by
  constructor
  · constructor; constructor
  constructor
  · constructor; constructor; constructor
  constructor
  · intro ctx
    simp [Level.eval]
    grind
  · constructor
    · simp [Level.eval]
    · simp [Level.eval]

/-
theorem Level.forall_param_le_eval_max (balance : Int) (l1 l2 : Level) (p : Name)
  (hwf1: l1.NF) (hwf2 : l2.NF) :
   (∀ (ctx : Name → Nat), ↑(ctx p) ≤ ↑((l1.max l2).eval ctx) + balance) →
   (∀ (ctx : Name → Nat), ↑(ctx p) ≤ ↑(l1.eval ctx) + balance) ∨ (∀ (ctx : Name → Nat), ↑(ctx p) ≤ ↑(l2.eval ctx) + balance) := by
  simp [Level.forall_param_le_eval, hwf1, hwf2, NF.max, coeff]
  simp [eval]
  intro hle_max c hcoeff hle1
  rw [Lean.Omega.Int.ofNat_max] at hle_max
  rw [← Int.max_add_right] at hle_max
  cases hc1 : l1.coeff p <;> cases hc2 : l2.coeff p <;> simp [hc1, hc2] at hcoeff
  case none.some =>
    subst hcoeff


  have hle_max : 0 ≤ (↑(l1.eval fun x => 0) + balance) ∨ 0 ≤ (↑(l2.eval fun x => 0) + balance) := by grind
  cases hle_max <;> clear hle_max
  case inl hl1 =>
    left
    constructor
    · assumption
    ·         constructor
        ·
        · grind
      case some.none =>
-/
#exit



theorem Level.forall_param_le_eval' (balance : Int) (l : Level) (p : Name) :
  (∀ ctx, ctx p ≤ l.eval ctx + balance) ↔
  (∀ n, n ≤ l.eval (fun n' => if n' = p then n else 0) + balance) := by
  constructor
  · intro h n
    specialize h (fun n' => if n' = p then n else 0)
    grind
  · intro h ctx
    specialize h (ctx p)
    have := Level.eval_mono (fun n' => if n' = p then ctx p else 0) ctx l (by grind)
    simp_all
    grind

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
    simp [eval.eq_5] at *
    rw [Level.forall_param_le_eval] at *
    simp [eval, coeff] at *
    grind
    sorry
  case case10 => -- zero le max
    simp only [Bool.or_eq_true]
    simp [eval.eq_1, Level.forall_zero_le_eval] at *
    grind [eval.eq_3]
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
