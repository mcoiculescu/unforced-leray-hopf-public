import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_1.Route
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!


Source of record: `the November 2 reference manuscript`, lines 2100-2105 (the
regular backward problem, "Duhamel for a smooth compactly supported datum", treated by the source
as standard parabolic theory) and 2085-2093 (`TrainClose` bounds only `D^j v` for `j ≤ 4`, whence
the LOCAL regularity).  This file fixes the classes in which the local gain of one derivative is
proved; `Sub/PartIIb_T22_2_3_1_6.lean` has the leaves and the proof `locStep_of`.

* `CB T m Z`: `Z` is `C^m_b` on `[0, T] × ℝ²`: recursively, jointly continuous and bounded, with
  differentiable slices whose two partials are of class `CB T (m - 1)`;
* `CBle T m Z b`: every partial of order `≤ m` of `Z` is bounded by `b σ` at time `σ`;
* `CBL T R m V`: the same as `CB` on the band `band R` (the form of `LocCk`, `locCk_cbl`);
* `EtaS T R Z`: `Z` vanishes for `|η| > R`; `OffBand T R Z`: `Z` vanishes for `|η| < R`;
* `IsCut R ψ`: `ψ : ℝ → ℝ` smooth, vanishing for `|t| > R`; `cutF ψ` is the corresponding function
  of `η`, `mulC ψ Z` the product.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.BwdRoute

namespace LS

open CylPDE

/-! ## The classes -/

/-- `C⁰_b` on `[0, T] × ℝ²`: jointly continuous and bounded. -/
def CB0 (T : ℝ) (Z : ℝ → Pl → ℝ) : Prop :=
  ContinuousOn (fun z : ℝ × Pl => Z z.1 z.2) (Icc 0 T ×ˢ univ) ∧
    ∃ C : ℝ, ∀ σ ∈ Icc 0 T, ∀ x : Pl, |Z σ x| ≤ C

/-- `C^m_b` on `[0, T] × ℝ²`, recursively in `m`. -/
def CB (T : ℝ) : ℕ → (ℝ → Pl → ℝ) → Prop
  | 0, Z => CB0 T Z
  | m + 1, Z => CB0 T Z ∧ (∀ σ ∈ Icc 0 T, Differentiable ℝ (Z σ)) ∧
      ∀ j : Fin 2, CB T m (fun σ => B0579.pd j (Z σ))

/-- Every partial of order `≤ m` of `Z` is bounded by `b σ` at time `σ ∈ [0, T]`. -/
def CBle (T : ℝ) : ℕ → (ℝ → Pl → ℝ) → (ℝ → ℝ) → Prop
  | 0, Z, b => ∀ σ ∈ Icc 0 T, ∀ x : Pl, |Z σ x| ≤ b σ
  | m + 1, Z, b => (∀ σ ∈ Icc 0 T, ∀ x : Pl, |Z σ x| ≤ b σ) ∧
      ∀ j : Fin 2, CBle T m (fun σ => B0579.pd j (Z σ)) b

/-- `Z` vanishes for `|η| > R`, on `[0, T]`. -/
def EtaS (T R : ℝ) (Z : ℝ → Pl → ℝ) : Prop :=
  ∀ σ ∈ Icc 0 T, ∀ x : Pl, R < |x.2| → Z σ x = 0

/-- `Z` vanishes for `|η| < R`, on `[0, T]`. -/
def OffBand (T R : ℝ) (Z : ℝ → Pl → ℝ) : Prop :=
  ∀ σ ∈ Icc 0 T, ∀ x : Pl, |x.2| < R → Z σ x = 0

/-- A cutoff in `η`: smooth, vanishing for `|t| > R`. -/
structure IsCut (R : ℝ) (ψ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ
  supp : ∀ t : ℝ, R < |t| → ψ t = 0

/-- A function of `η` as a time-independent family. -/
def cutF (ψ : ℝ → ℝ) : ℝ → Pl → ℝ := fun _ x => ψ x.2

/-- The product `ψ(η) Z`. -/
def mulC (ψ : ℝ → ℝ) (Z : ℝ → Pl → ℝ) : ℝ → Pl → ℝ := fun σ x => ψ x.2 * Z σ x

/-- The partial `∂_j` of a function of `η`, as a function of `η`: `0` for `j = 0`, `ψ'` for
`j = 1`. -/
def dCut (ψ : ℝ → ℝ) (j : Fin 2) : ℝ → ℝ := if j = 0 then fun _ => 0 else deriv ψ

/-- The drift term `b·∇Z`. -/
def trm (b0 b1 Z : ℝ → Pl → ℝ) : ℝ → Pl → ℝ :=
  fun σ x => b0 σ x * B0579.pd 0 (Z σ) x + b1 σ x * B0579.pd 1 (Z σ) x

/-! ## Calculus of `pd` -/

theorem pd_add {f g : Pl → ℝ} {x : Pl} (j : Fin 2) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    B0579.pd j (fun y => f y + g y) x = B0579.pd j f x + B0579.pd j g x := by
  unfold B0579.pd
  rw [fderiv_fun_add hf hg]
  rfl

theorem pd_mul {f g : Pl → ℝ} {x : Pl} (j : Fin 2) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    B0579.pd j (fun y => f y * g y) x = f x * B0579.pd j g x + g x * B0579.pd j f x := by
  unfold B0579.pd
  rw [fderiv_fun_mul hf hg]
  simp [smul_eq_mul]

theorem pd_const (j : Fin 2) (c : ℝ) (x : Pl) : B0579.pd j (fun _ : Pl => c) x = 0 := by
  unfold B0579.pd
  simp

theorem pd_congr_of_eventuallyEq {f g : Pl → ℝ} {x : Pl} (j : Fin 2) (h : f =ᶠ[𝓝 x] g) :
    B0579.pd j f x = B0579.pd j g x := by
  unfold B0579.pd
  rw [h.fderiv_eq]

theorem isOpen_lt_abs (R : ℝ) : IsOpen {y : Pl | R < |y.2|} :=
  isOpen_lt continuous_const continuous_snd.abs

theorem isOpen_band (R : ℝ) : IsOpen (band R) := by
  unfold band
  exact isOpen_lt continuous_snd.abs continuous_const

/-- `fderiv` in terms of the two partials. -/
theorem fderiv_eq_pd (f : Pl → ℝ) (x : Pl) :
    fderiv ℝ f x = (B0579.pd 0 f x) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (B0579.pd 1 f x) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  ext
  · simp [B0579.pd, B0579.dir]
  · simp [B0579.pd, B0579.dir]

/-! ## The class `CB` -/

variable {T : ℝ}

theorem CB.cb0 : ∀ {m : ℕ} {Z : ℝ → Pl → ℝ}, CB T m Z → CB0 T Z
  | 0, _, h => h
  | _ + 1, _, h => h.1

theorem CB.mono_succ : ∀ (m : ℕ) (Z : ℝ → Pl → ℝ), CB T (m + 1) Z → CB T m Z
  | 0, _, h => h.1
  | m + 1, _, h => ⟨h.1, h.2.1, fun j => CB.mono_succ m _ (h.2.2 j)⟩

theorem CB.mono {m n : ℕ} (hmn : m ≤ n) {Z : ℝ → Pl → ℝ} (h : CB T n Z) : CB T m Z := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ih (CB.mono_succ n Z h)

theorem CB.pd {m : ℕ} {Z : ℝ → Pl → ℝ} (h : CB T (m + 1) Z) (j : Fin 2) :
    CB T m (fun σ => B0579.pd j (Z σ)) := h.2.2 j

theorem CB.diff {m : ℕ} {Z : ℝ → Pl → ℝ} (h : CB T (m + 1) Z) :
    ∀ σ ∈ Icc 0 T, Differentiable ℝ (Z σ) := h.2.1

theorem CB0.congr {Z Z' : ℝ → Pl → ℝ} (h : CB0 T Z)
    (e : ∀ σ ∈ Icc 0 T, ∀ x : Pl, Z σ x = Z' σ x) : CB0 T Z' := by
  obtain ⟨hc, C, hC⟩ := h
  refine ⟨hc.congr fun z hz => (e z.1 hz.1 z.2).symm, C, fun σ hσ x => ?_⟩
  rw [← e σ hσ x]
  exact hC σ hσ x

theorem CB.congr : ∀ {m : ℕ} {Z Z' : ℝ → Pl → ℝ}, CB T m Z →
    (∀ σ ∈ Icc 0 T, ∀ x : Pl, Z σ x = Z' σ x) → CB T m Z'
  | 0, _, _, h, e => CB0.congr h e
  | m + 1, Z, Z', h, e => by
      have hfun : ∀ σ ∈ Icc 0 T, Z σ = Z' σ := fun σ hσ => funext (e σ hσ)
      refine ⟨CB0.congr h.1 e, fun σ hσ => hfun σ hσ ▸ h.2.1 σ hσ, fun j => ?_⟩
      refine CB.congr (h.2.2 j) fun σ hσ x => ?_
      rw [hfun σ hσ]

theorem CB0.add {Z Z' : ℝ → Pl → ℝ} (h : CB0 T Z) (h' : CB0 T Z') :
    CB0 T (fun σ x => Z σ x + Z' σ x) := by
  obtain ⟨hc, C, hC⟩ := h
  obtain ⟨hc', C', hC'⟩ := h'
  refine ⟨hc.add hc', C + C', fun σ hσ x => ?_⟩
  exact (abs_add_le _ _).trans (add_le_add (hC σ hσ x) (hC' σ hσ x))

theorem CB.add : ∀ {m : ℕ} {Z Z' : ℝ → Pl → ℝ}, CB T m Z → CB T m Z' →
    CB T m (fun σ x => Z σ x + Z' σ x)
  | 0, _, _, h, h' => CB0.add h h'
  | m + 1, Z, Z', h, h' => by
      refine ⟨CB0.add h.1 h'.1, fun σ hσ => (h.2.1 σ hσ).add (h'.2.1 σ hσ), fun j => ?_⟩
      refine CB.congr (CB.add (h.2.2 j) (h'.2.2 j)) fun σ hσ x => ?_
      exact (pd_add j (h.2.1 σ hσ x) (h'.2.1 σ hσ x)).symm

theorem CB0.mul {A B : ℝ → Pl → ℝ} (h : CB0 T A) (h' : CB0 T B) :
    CB0 T (fun σ x => A σ x * B σ x) := by
  obtain ⟨hc, C, hC⟩ := h
  obtain ⟨hc', C', hC'⟩ := h'
  refine ⟨hc.mul hc', C * C', fun σ hσ x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC σ hσ x) (hC' σ hσ x) (abs_nonneg _) ((abs_nonneg _).trans (hC σ hσ x))

theorem CB.mul : ∀ {m : ℕ} {A B : ℝ → Pl → ℝ}, CB T m A → CB T m B →
    CB T m (fun σ x => A σ x * B σ x)
  | 0, _, _, h, h' => CB0.mul h h'
  | m + 1, A, B, h, h' => by
      refine ⟨CB0.mul h.1 h'.1, fun σ hσ => (h.2.1 σ hσ).mul (h'.2.1 σ hσ), fun j => ?_⟩
      refine CB.congr (CB.add (CB.mul (CB.mono_succ m _ h) (h'.2.2 j))
        (CB.mul (CB.mono_succ m _ h') (h.2.2 j))) fun σ hσ x => ?_
      exact (pd_mul j (h.2.1 σ hσ x) (h'.2.1 σ hσ x)).symm

theorem CB.const (m : ℕ) (c : ℝ) : CB T m (fun _ _ => c) := by
  induction m generalizing c with
  | zero => exact ⟨continuousOn_const, |c|, fun _ _ _ => le_rfl⟩
  | succ m ih =>
      refine ⟨⟨continuousOn_const, |c|, fun _ _ _ => le_rfl⟩, fun _ _ => differentiable_const c,
        fun j => ?_⟩
      exact CB.congr (ih 0) fun σ _ x => (pd_const j c x).symm

theorem CB.const_mul {m : ℕ} (c : ℝ) {Z : ℝ → Pl → ℝ} (h : CB T m Z) :
    CB T m (fun σ x => c * Z σ x) := CB.mul (CB.const m c) h

theorem CB.neg {m : ℕ} {Z : ℝ → Pl → ℝ} (h : CB T m Z) : CB T m (fun σ x => -Z σ x) :=
  CB.congr (CB.const_mul (-1) h) fun _ _ _ => by ring

theorem CB.sub {m : ℕ} {Z Z' : ℝ → Pl → ℝ} (h : CB T m Z) (h' : CB T m Z') :
    CB T m (fun σ x => Z σ x - Z' σ x) :=
  CB.congr (CB.add h (CB.neg h')) fun _ _ _ => by ring

/-- A family of class `CB T m` has `C^m` slices. -/
theorem CB.contDiff : ∀ {m : ℕ} {Z : ℝ → Pl → ℝ}, CB T m Z → ∀ σ ∈ Icc 0 T,
    ContDiff ℝ m (Z σ)
  | 0, Z, h, σ, hσ => by
      have hc : Continuous (Z σ) := continuousOn_univ.1 ((CB.cb0 h).1.comp
        (continuousOn_const (c := σ) |>.prodMk continuousOn_id) (fun x _ => ⟨hσ, mem_univ x⟩))
      exact contDiff_zero.2 hc
  | m + 1, Z, h, σ, hσ => by
      have hcast : ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 := by norm_cast
      rw [hcast, contDiff_succ_iff_fderiv]
      refine ⟨h.2.1 σ hσ, by simp, ?_⟩
      have key : fderiv ℝ (Z σ) = fun x => (B0579.pd 0 (Z σ) x) • ContinuousLinearMap.fst ℝ ℝ ℝ +
          (B0579.pd 1 (Z σ) x) • ContinuousLinearMap.snd ℝ ℝ ℝ := funext (fderiv_eq_pd (Z σ))
      rw [key]
      exact ((CB.contDiff (h.2.2 0) σ hσ).smul contDiff_const).add
        ((CB.contDiff (h.2.2 1) σ hσ).smul contDiff_const)

/-- The slices of a `CB T m` family with `m ≥ 2` have symmetric second partials. -/
theorem pd_comm_of_contDiff {f : Pl → ℝ} (hf : ContDiff ℝ 2 f) (i j : Fin 2) (x : Pl) :
    B0579.pd i (B0579.pd j f) x = B0579.pd j (B0579.pd i f) x := by
  have h1 : ∀ (u : Pl), DifferentiableAt ℝ (fderiv ℝ f) x := fun _ =>
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have hpd : ∀ k : Fin 2, B0579.pd k f = fun y => fderiv ℝ f y (B0579.dir k) := fun _ => rfl
  have hder : ∀ k l : Fin 2, B0579.pd k (B0579.pd l f) x =
      fderiv ℝ (fderiv ℝ f) x (B0579.dir k) (B0579.dir l) := by
    intro k l
    unfold B0579.pd
    have hd := (h1 x).hasFDerivAt.clm_apply (hasFDerivAt_const (B0579.dir l) x)
    have := hd.fderiv
    simp only [ContinuousLinearMap.comp_zero, zero_add] at this
    rw [show (fun y => fderiv ℝ f y (B0579.dir l)) = _ from rfl, this]
    rfl
  rw [hder, hder]
  have hsym := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  exact hsym _ _

/-! ## The bound `CBle` -/

theorem CBle.top {m : ℕ} {Z : ℝ → Pl → ℝ} {b : ℝ → ℝ} (h : CBle T m Z b) :
    ∀ σ ∈ Icc 0 T, ∀ x : Pl, |Z σ x| ≤ b σ := by
  cases m with
  | zero => exact h
  | succ m => exact h.1

theorem CBle.mono_succ : ∀ (m : ℕ) (Z : ℝ → Pl → ℝ) (b : ℝ → ℝ), CBle T (m + 1) Z b → CBle T m Z b
  | 0, _, _, h => h.1
  | m + 1, _, _, h => ⟨h.1, fun j => CBle.mono_succ m _ _ (h.2 j)⟩

theorem CBle.mono_b : ∀ {m : ℕ} {Z : ℝ → Pl → ℝ} {b b' : ℝ → ℝ}, CBle T m Z b →
    (∀ σ ∈ Icc 0 T, b σ ≤ b' σ) → CBle T m Z b'
  | 0, _, _, _, h, e => fun σ hσ x => (h σ hσ x).trans (e σ hσ)
  | m + 1, _, _, _, h, e => ⟨fun σ hσ x => (h.1 σ hσ x).trans (e σ hσ),
      fun j => CBle.mono_b (h.2 j) e⟩

theorem CBle.congr : ∀ {m : ℕ} {Z Z' : ℝ → Pl → ℝ} {b : ℝ → ℝ}, CBle T m Z b →
    (∀ σ ∈ Icc 0 T, ∀ x : Pl, Z σ x = Z' σ x) → CBle T m Z' b
  | 0, _, _, _, h, e => fun σ hσ x => by rw [← e σ hσ x]; exact h σ hσ x
  | m + 1, Z, Z', _, h, e => by
      have hfun : ∀ σ ∈ Icc 0 T, Z σ = Z' σ := fun σ hσ => funext (e σ hσ)
      refine ⟨fun σ hσ x => by rw [← e σ hσ x]; exact h.1 σ hσ x, fun j => ?_⟩
      refine CBle.congr (h.2 j) fun σ hσ x => ?_
      rw [hfun σ hσ]

theorem CBle.add : ∀ {m : ℕ} {Z Z' : ℝ → Pl → ℝ} {b b' : ℝ → ℝ}, CB T m Z → CB T m Z' →
    CBle T m Z b → CBle T m Z' b' → CBle T m (fun σ x => Z σ x + Z' σ x) (fun σ => b σ + b' σ)
  | 0, _, _, _, _, _, _, h, h' => fun σ hσ x =>
      (abs_add_le _ _).trans (add_le_add (h σ hσ x) (h' σ hσ x))
  | m + 1, Z, Z', _, _, hc, hc', h, h' => by
      refine ⟨fun σ hσ x => (abs_add_le _ _).trans (add_le_add (h.1 σ hσ x) (h'.1 σ hσ x)),
        fun j => ?_⟩
      refine CBle.congr (CBle.add (hc.2.2 j) (hc'.2.2 j) (h.2 j) (h'.2 j)) fun σ hσ x => ?_
      exact (pd_add j (hc.2.1 σ hσ x) (hc'.2.1 σ hσ x)).symm

/-- Leibniz bound: `∂^α (AB)`, `|α| ≤ m`, is bounded by `2^m C b` when `A` has bound `C` and `B`
has bound `b`. -/
theorem CBle.mul : ∀ {m : ℕ} {A B : ℝ → Pl → ℝ} {C : ℝ} {b : ℝ → ℝ}, 0 ≤ C →
    (∀ σ ∈ Icc 0 T, 0 ≤ b σ) → CB T m A → CB T m B → CBle T m A (fun _ => C) → CBle T m B b →
    CBle T m (fun σ x => A σ x * B σ x) (fun σ => 2 ^ m * C * b σ)
  | 0, A, B, C, b, hC, hb, _, _, h, h' => fun σ hσ x => by
      rw [abs_mul]
      have := mul_le_mul (h σ hσ x) (h' σ hσ x) (abs_nonneg _) hC
      simpa using this
  | m + 1, A, B, C, b, hC, hb, hc, hc', h, h' => by
      refine ⟨fun σ hσ x => ?_, fun j => ?_⟩
      · rw [abs_mul]
        have h1 := mul_le_mul (h.1 σ hσ x) (h'.1 σ hσ x) (abs_nonneg _) hC
        have h2 : (1 : ℝ) ≤ 2 ^ (m + 1) := one_le_pow₀ (by norm_num)
        have h3 : 0 ≤ C * b σ := mul_nonneg hC (hb σ hσ)
        calc |A σ x| * |B σ x| ≤ C * b σ := h1
          _ ≤ 2 ^ (m + 1) * (C * b σ) := le_mul_of_one_le_left h3 h2
          _ = 2 ^ (m + 1) * C * b σ := by ring
      · have h1 := CBle.mul hC hb (CB.mono_succ m _ hc) (hc'.2.2 j) (CBle.mono_succ m _ _ h) (h'.2 j)
        have h2 : CBle T m (fun σ x => B0579.pd j (A σ) x * B σ x) (fun σ => 2 ^ m * C * b σ) :=
          CBle.mul hC hb (hc.2.2 j) (CB.mono_succ m _ hc') (h.2 j) (CBle.mono_succ m _ _ h')
        have h3 := CBle.add (CB.mul (CB.mono_succ m _ hc) (hc'.2.2 j))
          (CB.mul (hc.2.2 j) (CB.mono_succ m _ hc')) h1 h2
        refine CBle.mono_b (CBle.congr h3 fun σ hσ x => ?_) fun σ _ => ?_
        · rw [pd_mul j (hc.2.1 σ hσ x) (hc'.2.1 σ hσ x)]
          ring
        · apply le_of_eq
          ring

/-- A family of class `CB T m` has a uniform bound on its partials of order `≤ m`. -/
theorem CB.exists_le : ∀ {m : ℕ} {Z : ℝ → Pl → ℝ}, CB T m Z →
    ∃ M : ℝ, 0 ≤ M ∧ CBle T m Z (fun _ => M)
  | 0, _, h => by
      obtain ⟨_, C, hC⟩ := h
      exact ⟨|C|, abs_nonneg _, fun σ hσ x => (hC σ hσ x).trans (le_abs_self _)⟩
  | m + 1, _, h => by
      obtain ⟨_, C, hC⟩ := h.1
      obtain ⟨M0, hM0, h0⟩ := CB.exists_le (h.2.2 0)
      obtain ⟨M1, hM1, h1⟩ := CB.exists_le (h.2.2 1)
      refine ⟨|C| + M0 + M1, by positivity, fun σ hσ x => ?_, fun j => ?_⟩
      · exact (hC σ hσ x).trans ((le_abs_self _).trans (by linarith))
      · have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
        rcases hj with rfl | rfl
        · exact CBle.mono_b h0 fun _ _ => by linarith [abs_nonneg C]
        · exact CBle.mono_b h1 fun _ _ => by linarith [abs_nonneg C]

/-! ## Supports in `η` -/

theorem EtaS.pd {R : ℝ} {Z : ℝ → Pl → ℝ} (h : EtaS T R Z) (j : Fin 2) :
    EtaS T R (fun σ => B0579.pd j (Z σ)) := by
  intro σ hσ x hx
  have hev : Z σ =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem ((isOpen_lt_abs R).mem_nhds hx) fun y hy => h σ hσ y hy
  show B0579.pd j (Z σ) x = 0
  rw [pd_congr_of_eventuallyEq j hev, pd_const]

theorem OffBand.pd {R : ℝ} {Z : ℝ → Pl → ℝ} (h : OffBand T R Z) (j : Fin 2) :
    OffBand T R (fun σ => B0579.pd j (Z σ)) := by
  intro σ hσ x hx
  have hev : Z σ =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem ((isOpen_band R).mem_nhds hx) fun y hy => h σ hσ y hy
  show B0579.pd j (Z σ) x = 0
  rw [pd_congr_of_eventuallyEq j hev, pd_const]

theorem EtaS.mul_left {R : ℝ} {Z : ℝ → Pl → ℝ} (A : ℝ → Pl → ℝ) (h : EtaS T R Z) :
    EtaS T R (fun σ x => A σ x * Z σ x) := fun σ hσ x hx => by
  simp [h σ hσ x hx]

theorem EtaS.mul_right {R : ℝ} {Z : ℝ → Pl → ℝ} (A : ℝ → Pl → ℝ) (h : EtaS T R Z) :
    EtaS T R (fun σ x => Z σ x * A σ x) := fun σ hσ x hx => by
  simp [h σ hσ x hx]

theorem EtaS.add {R : ℝ} {Z Z' : ℝ → Pl → ℝ} (h : EtaS T R Z) (h' : EtaS T R Z') :
    EtaS T R (fun σ x => Z σ x + Z' σ x) := fun σ hσ x hx => by
  simp [h σ hσ x hx, h' σ hσ x hx]

theorem EtaS.neg {R : ℝ} {Z : ℝ → Pl → ℝ} (h : EtaS T R Z) :
    EtaS T R (fun σ x => -Z σ x) := fun σ hσ x hx => by
  simp [h σ hσ x hx]

theorem EtaS.mono {R R' : ℝ} (hR : R ≤ R') {Z : ℝ → Pl → ℝ} (h : EtaS T R Z) : EtaS T R' Z :=
  fun σ hσ x hx => h σ hσ x (lt_of_le_of_lt hR hx)

theorem OffBand.mul_left {R : ℝ} {Z : ℝ → Pl → ℝ} (A : ℝ → Pl → ℝ) (h : OffBand T R Z) :
    OffBand T R (fun σ x => A σ x * Z σ x) := fun σ hσ x hx => by
  simp [h σ hσ x hx]

theorem OffBand.add {R : ℝ} {Z Z' : ℝ → Pl → ℝ} (h : OffBand T R Z) (h' : OffBand T R Z') :
    OffBand T R (fun σ x => Z σ x + Z' σ x) := fun σ hσ x hx => by
  simp [h σ hσ x hx, h' σ hσ x hx]

/-! ## Cutoffs -/

theorem IsCut.deriv {R : ℝ} {ψ : ℝ → ℝ} (h : IsCut R ψ) : IsCut R (deriv ψ) where
  smooth := (contDiff_infty_iff_deriv.1 h.smooth).2
  supp t ht := by
    have hU : IsOpen {s : ℝ | R < |s|} := isOpen_lt continuous_const continuous_abs
    have hev : ψ =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (hU.mem_nhds ht) fun s hs => h.supp s hs
    rw [hev.deriv_eq]
    simp

theorem IsCut.dCut {R : ℝ} {ψ : ℝ → ℝ} (h : IsCut R ψ) (j : Fin 2) : IsCut R (dCut ψ j) := by
  unfold LS.dCut
  split_ifs
  · exact ⟨contDiff_const, fun _ _ => rfl⟩
  · exact h.deriv

theorem IsCut.differentiable {R : ℝ} {ψ : ℝ → ℝ} (h : IsCut R ψ) : Differentiable ℝ ψ :=
  h.smooth.differentiable (by simp)

theorem IsCut.continuous {R : ℝ} {ψ : ℝ → ℝ} (h : IsCut R ψ) : Continuous ψ := h.smooth.continuous

theorem IsCut.exists_bound {R : ℝ} {ψ : ℝ → ℝ} (h : IsCut R ψ) : ∃ C : ℝ, ∀ t, |ψ t| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -|R|) (b := |R|)).exists_bound_of_continuousOn
    h.continuous.continuousOn
  refine ⟨|C|, fun t => ?_⟩
  by_cases ht : R < |t|
  · rw [h.supp t ht, abs_zero]
    exact abs_nonneg _
  · have hmem : t ∈ Icc (-|R|) |R| := abs_le.1 ((not_lt.1 ht).trans (le_abs_self R))
    have := hC t hmem
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)

/-- The partial of a function of `η`. -/
theorem pd_cut {ψ : ℝ → ℝ} (hψ : Differentiable ℝ ψ) (j : Fin 2) (x : Pl) :
    B0579.pd j (fun y : Pl => ψ y.2) x = dCut ψ j x.2 := by
  have hc : HasFDerivAt (fun y : Pl => ψ y.2)
      ((_root_.deriv ψ x.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    (hψ x.2).hasDerivAt.comp_hasFDerivAt x hasFDerivAt_snd
  unfold B0579.pd dCut
  rw [hc.fderiv]
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hj with rfl | rfl
  · simp [B0579.dir]
  · simp [B0579.dir]

/-- A cutoff is a `CB` family of every order. -/
theorem IsCut.cb {R : ℝ} (m : ℕ) : ∀ {ψ : ℝ → ℝ}, IsCut R ψ → CB T m (cutF ψ) := by
  induction m with
  | zero =>
      intro ψ h
      obtain ⟨C, hC⟩ := h.exists_bound
      exact ⟨(h.continuous.comp (continuous_snd.comp continuous_snd)).continuousOn, C,
        fun _ _ x => hC x.2⟩
  | succ m ih =>
      intro ψ h
      obtain ⟨C, hC⟩ := h.exists_bound
      refine ⟨⟨(h.continuous.comp (continuous_snd.comp continuous_snd)).continuousOn, C,
        fun _ _ x => hC x.2⟩, fun _ _ => h.differentiable.comp differentiable_snd, fun j => ?_⟩
      refine CB.congr (ih (h.dCut j)) fun σ _ x => ?_
      exact (pd_cut h.differentiable j x).symm

theorem IsCut.etaS {R : ℝ} {ψ : ℝ → ℝ} (h : IsCut R ψ) : EtaS T R (cutF ψ) :=
  fun _ _ x hx => h.supp x.2 hx

/-- Existence of cutoffs with a plateau. -/
theorem exists_cut {R₁ R₂ : ℝ} (h1 : 0 < R₁) (h2 : R₁ < R₂) :
    ∃ ψ : ℝ → ℝ, IsCut R₂ ψ ∧ ∀ t : ℝ, |t| ≤ R₁ → ψ t = 1 := by
  let f : ContDiffBump (0 : ℝ) := ⟨R₁, R₂, h1, h2⟩
  refine ⟨f, ⟨f.contDiff, fun t ht => ?_⟩, fun t ht => ?_⟩
  · apply f.zero_of_le_dist
    show R₂ ≤ dist t 0
    rw [Real.dist_eq, sub_zero]
    exact ht.le
  · apply f.one_of_mem_closedBall
    show t ∈ Metric.closedBall (0 : ℝ) R₁
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact ht

/-- On the plateau of a cutoff the derivative vanishes. -/
theorem deriv_eq_zero_of_plateau {ψ : ℝ → ℝ} {R₁ : ℝ} (h : ∀ t : ℝ, |t| ≤ R₁ → ψ t = 1) {t : ℝ}
    (ht : |t| < R₁) : deriv ψ t = 0 := by
  have hU : IsOpen {s : ℝ | |s| < R₁} := isOpen_lt continuous_abs continuous_const
  have hev : ψ =ᶠ[𝓝 t] fun _ => (1 : ℝ) :=
    Filter.eventually_of_mem (hU.mem_nhds ht) fun s hs => h s (le_of_lt hs)
  rw [hev.deriv_eq]
  simp

/-! ## The local class -/

/-- `C⁰_b` on `[0, T] × band R`. -/
def CBL0 (T R : ℝ) (V : ℝ → Pl → ℝ) : Prop :=
  ContinuousOn (fun z : ℝ × Pl => V z.1 z.2) (Icc 0 T ×ˢ band R) ∧
    ∃ C : ℝ, ∀ σ ∈ Icc 0 T, ∀ x ∈ band R, |V σ x| ≤ C

/-- `C^m_b` on `[0, T] × band R`, recursively in `m`. -/
def CBL (T R : ℝ) : ℕ → (ℝ → Pl → ℝ) → Prop
  | 0, V => CBL0 T R V
  | m + 1, V => CBL0 T R V ∧ (∀ σ ∈ Icc 0 T, DifferentiableOn ℝ (V σ) (band R)) ∧
      ∀ j : Fin 2, CBL T R m (fun σ => B0579.pd j (V σ))

theorem CBL.cb0 {R : ℝ} : ∀ {m : ℕ} {V : ℝ → Pl → ℝ}, CBL T R m V → CBL0 T R V
  | 0, _, h => h
  | _ + 1, _, h => h.1

theorem CBL.mono_succ {R : ℝ} : ∀ (m : ℕ) (V : ℝ → Pl → ℝ), CBL T R (m + 1) V → CBL T R m V
  | 0, _, h => h.1
  | m + 1, _, h => ⟨h.1, h.2.1, fun j => CBL.mono_succ m _ (h.2.2 j)⟩

theorem CBL.mono {R : ℝ} {m n : ℕ} (hmn : m ≤ n) {V : ℝ → Pl → ℝ} (h : CBL T R n V) :
    CBL T R m V := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ih (CBL.mono_succ n V h)

/-- `pdW` of a `C^k` function on an open band is `C^(k - |l|)`. -/
theorem contDiffOn_pdW {R : ℝ} {k : ℕ} {g : Pl → ℝ} (hg : ContDiffOn ℝ k g (band R)) :
    ∀ (l : List (Fin 2)), l.length ≤ k → ContDiffOn ℝ ((k - l.length : ℕ) : WithTop ℕ∞) (pdW l g) (band R)
  | [], _ => by simpa [pdW] using hg
  | j :: l, hl => by
      have hl' : l.length + 1 ≤ k := by simpa using hl
      have h := contDiffOn_pdW hg l (by omega)
      have hcast : (((k - (j :: l).length : ℕ) : WithTop ℕ∞) + 1) ≤
          ((k - l.length : ℕ) : WithTop ℕ∞) := by
        have : k - (j :: l).length + 1 = k - l.length := by
          simp only [List.length_cons]
          omega
        exact_mod_cast this.le
      have hd := h.fderiv_of_isOpen (isOpen_band R) hcast
      exact hd.clm_apply contDiffOn_const

/-- `LocCk` gives the recursive local class for every word. -/
theorem locCk_cbl_word {R : ℝ} {k : ℕ} {u : ℝ → Pl → ℝ} (h : LocCk T R k u) :
    ∀ (m : ℕ) (l : List (Fin 2)), l.length + m ≤ k → CBL T R m (fun σ => pdW l (u σ))
  | 0, l, hl => ⟨h.cont l (by omega), h.bdd l (by omega)⟩
  | m + 1, l, hl => by
      refine ⟨⟨h.cont l (by omega), h.bdd l (by omega)⟩, fun σ hσ => ?_, fun j => ?_⟩
      · have h1 := contDiffOn_pdW (h.slice σ hσ) l (by omega)
        exact h1.differentiableOn (by
          have : k - l.length ≠ 0 := by omega
          exact_mod_cast this)
      · exact locCk_cbl_word h m (j :: l) (by simp only [List.length_cons]; omega)

theorem locCk_cbl {R : ℝ} {k : ℕ} {u : ℝ → Pl → ℝ} (h : LocCk T R k u) : CBL T R k u := by
  simpa [pdW] using locCk_cbl_word h k [] (by simp)

/-- A cutoff supported inside the band turns the local class into the global one. -/
theorem CBL.cut {R R' : ℝ} (hR : R' < R) (m : ℕ) : ∀ {ψ : ℝ → ℝ} {V : ℝ → Pl → ℝ},
    IsCut R' ψ → CBL T R m V → CB T m (mulC ψ V) := by
  have hzero : ∀ {ψ : ℝ → ℝ} {V : ℝ → Pl → ℝ}, IsCut R' ψ → CBL0 T R V → CB0 T (mulC ψ V) := by
    intro ψ V hψ hV
    obtain ⟨hc, C, hC⟩ := hV
    obtain ⟨Cψ, hCψ⟩ := hψ.exists_bound
    refine ⟨fun z hz => ?_, Cψ * |C|, fun σ hσ x => ?_⟩
    · by_cases hzb : |z.2.2| < R
      · have hzb' : z.2 ∈ band R := hzb
        have h1 : ContinuousWithinAt (fun z : ℝ × Pl => V z.1 z.2) (Icc 0 T ×ˢ band R) z :=
          hc z ⟨hz.1, hzb'⟩
        have h2 : ContinuousWithinAt (fun z : ℝ × Pl => ψ z.2.2) (Icc 0 T ×ˢ band R) z :=
          (hψ.continuous.comp (continuous_snd.comp continuous_snd)).continuousWithinAt
        have h3 := h2.mul h1
        refine h3.mono_of_mem_nhdsWithin ?_
        have hopen : IsOpen ((univ : Set ℝ) ×ˢ band R) := isOpen_univ.prod (isOpen_band R)
        have hnhds := inter_mem_nhdsWithin (Icc 0 T ×ˢ univ : Set (ℝ × Pl))
          (hopen.mem_nhds (⟨mem_univ _, hzb'⟩ : z ∈ (univ : Set ℝ) ×ˢ band R))
        exact Filter.mem_of_superset hnhds fun w hw => ⟨hw.1.1, hw.2.2⟩
      · have hU : IsOpen {w : ℝ × Pl | R' < |w.2.2|} :=
          isOpen_lt continuous_const (continuous_snd.comp continuous_snd).abs
        have hz' : z ∈ {w : ℝ × Pl | R' < |w.2.2|} := lt_of_lt_of_le hR (not_lt.1 hzb)
        have hev : (fun w : ℝ × Pl => mulC ψ V w.1 w.2) =ᶠ[𝓝 z] fun _ => (0 : ℝ) :=
          Filter.eventually_of_mem (hU.mem_nhds hz') fun w hw => by
            simp [mulC, hψ.supp _ hw]
        exact ((continuousAt_const.congr hev.symm)).continuousWithinAt
    · by_cases hx : |x.2| < R
      · show |ψ x.2 * V σ x| ≤ Cψ * |C|
        rw [abs_mul]
        exact mul_le_mul (hCψ _) ((hC σ hσ x hx).trans (le_abs_self _)) (abs_nonneg _)
          ((abs_nonneg _).trans (hCψ x.2))
      · have h0 : ψ x.2 = 0 := hψ.supp _ (lt_of_lt_of_le hR (not_lt.1 hx))
        show |ψ x.2 * V σ x| ≤ Cψ * |C|
        rw [h0, zero_mul, abs_zero]
        exact mul_nonneg ((abs_nonneg _).trans (hCψ x.2)) (abs_nonneg _)
  induction m with
  | zero => intro ψ V hψ hV; exact hzero hψ hV
  | succ m ih =>
      intro ψ V hψ hV
      have hdiffAt : ∀ σ ∈ Icc 0 T, ∀ x : Pl, |x.2| < R → DifferentiableAt ℝ (V σ) x :=
        fun σ hσ x hx => (hV.2.1 σ hσ x hx).differentiableAt ((isOpen_band R).mem_nhds hx)
      have hcutd : Differentiable ℝ (fun y : Pl => ψ y.2) :=
        hψ.differentiable.comp differentiable_snd
      have hzeroNear : ∀ σ : ℝ, ∀ x : Pl, ¬ |x.2| < R →
          (fun y => mulC ψ V σ y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        intro σ x hx
        have hx' : x ∈ {y : Pl | R' < |y.2|} := lt_of_lt_of_le hR (not_lt.1 hx)
        exact Filter.eventually_of_mem ((isOpen_lt_abs R').mem_nhds hx') fun y hy => by
          simp [mulC, hψ.supp _ hy]
      refine ⟨hzero hψ hV.1, fun σ hσ x => ?_, fun j => ?_⟩
      · by_cases hx : |x.2| < R
        · exact (hcutd x).mul (hdiffAt σ hσ x hx)
        · exact ((differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq (hzeroNear σ x hx))
      · have h1 := ih (hψ.dCut j) (CBL.mono_succ m V hV)
        have h2 := ih hψ (hV.2.2 j)
        refine CB.congr (CB.add h1 h2) fun σ hσ x => ?_
        show dCut ψ j x.2 * V σ x + ψ x.2 * B0579.pd j (V σ) x = B0579.pd j (mulC ψ V σ) x
        by_cases hx : |x.2| < R
        · have := pd_mul j (hcutd x) (hdiffAt σ hσ x hx)
          rw [pd_cut hψ.differentiable j x] at this
          show _ = B0579.pd j (fun y => ψ y.2 * V σ y) x
          rw [this]
          ring
        · rw [pd_congr_of_eventuallyEq j (hzeroNear σ x hx), pd_const]
          have hx' : R' < |x.2| := lt_of_lt_of_le hR (not_lt.1 hx)
          rw [(hψ.dCut j).supp _ hx', hψ.supp _ hx']
          ring

/-- Words of a `CB` family. -/
theorem CB.pdW {m : ℕ} {V : ℝ → Pl → ℝ} (h : CB T m V) : ∀ (l : List (Fin 2)), l.length ≤ m →
    CB T (m - l.length) (fun σ => BwdRoute.pdW l (V σ))
  | [], _ => by simpa [BwdRoute.pdW] using h
  | j :: l, hl => by
      have hl' : l.length + 1 ≤ m := by simpa using hl
      have h1 := CB.pdW h l (by omega)
      have hm : m - l.length = (m - (j :: l).length) + 1 := by
        simp only [List.length_cons]
        omega
      rw [hm] at h1
      exact h1.2.2 j

/-- `pdW` only depends on the function near the point. -/
theorem pdW_congr_band {ρ : ℝ} {f g : Pl → ℝ} (e : ∀ x ∈ band ρ, f x = g x) :
    ∀ (l : List (Fin 2)), ∀ x ∈ band ρ, pdW l f x = pdW l g x
  | [], x, hx => e x hx
  | j :: l, x, hx => by
      show B0579.pd j (pdW l f) x = B0579.pd j (pdW l g) x
      apply pd_congr_of_eventuallyEq
      exact Filter.eventually_of_mem ((isOpen_band ρ).mem_nhds hx) fun y hy =>
        pdW_congr_band e l y hy

/-- A `CB` family agreeing with `u` on `band ρ` gives `LocCk` of `u`. -/
theorem locCk_of_CB {ρ : ℝ} {m : ℕ} {V u : ℝ → Pl → ℝ} (h : CB T m V)
    (e : ∀ σ ∈ Icc 0 T, ∀ x ∈ band ρ, V σ x = u σ x) : LocCk T ρ m u := by
  refine ⟨fun σ hσ => ?_, fun l hl => ?_, fun l hl => ?_⟩
  · have h1 := (CB.contDiff h σ hσ).contDiffOn (s := band ρ)
    exact h1.congr fun x hx => (e σ hσ x hx).symm
  · have h1 := (CB.pdW h l hl).cb0.1
    have h2 : ContinuousOn (fun z : ℝ × Pl => pdW l (V z.1) z.2) (Icc 0 T ×ˢ band ρ) :=
      h1.mono (Set.prod_mono subset_rfl (subset_univ _))
    exact h2.congr fun z hz => (pdW_congr_band (e z.1 hz.1) l z.2 hz.2).symm
  · obtain ⟨C, hC⟩ := (CB.pdW h l hl).cb0.2
    refine ⟨C, fun σ hσ x hx => ?_⟩
    rw [← pdW_congr_band (e σ hσ) l x hx]
    exact hC σ hσ x

end LS

end UnforcedLeray.Short.IIb.BwdRoute
