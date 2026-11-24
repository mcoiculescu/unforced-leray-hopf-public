import UnforcedLeray.Short.PartI.Sub.T02_1_3
import UnforcedLeray.Lib.TrainB.P0W1
import UnforcedLeray.Lib.TrainB.CellBridge
import UnforcedLeray.Units.B0151.Linf
import UnforcedLeray.Short.Spine.Proofs.EstDerivWordBridge
import UnforcedLeray.Short.Spine.Proofs.EstEuclidBridge

/-!
# Part I, task `PartI:T02/1/3/4`: the Sobolev bound on the periodic cylinder for smooth fields

Source of record: `the November 2 reference manuscript`, lines 261-288.

The target is `cylSmoothSobolevBound : CylSmoothSobolevBound` (`Short/PartI/Sub/T02_1_3.lean`).

Route (all auxiliary declarations are prefixed `csb_`):
* (c) norm identification: for a smooth periodic `f` and a word `u` of length `≤ k + 3`, the
  classical derivative `iterD u f` has cell `L²` norm at most `‖W.ofCylSmooth f‖`
  (`csb_deriv_le`, `csb_exists_idx`, `csb_comp_bound`);
* (a) real sup bound: `B0151.enorm_derivWord_le` on the cell `(0, c] × ℝ`, transported to the
  centred cell by `TrainB.eLpNorm_sq_b0151_eq_cyl` (`csb_sup_word`, `csb_sup_word_real`);
* (b) assembly: the components `f · i`, `Spine.norm_iteratedFDeriv_le_of_derivWord` and
  `Spine.norm_iteratedFDeriv_euclid2_le`, with the constant `C = 24 * 2 ^ (k + 1)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace UnforcedLeray.Short.PartI

local instance : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

/-! ### Words and directions -/

/-- The direction of a Boolean letter: `true` is `∂_q`, `false` is `∂_η`. -/
def csbDir : Bool → ℝ × ℝ
  | true => (1, 0)
  | false => (0, 1)

/-- The index of a Boolean letter among the two cylinder directions. -/
def csbLetter : Bool → Fin 2
  | true => 0
  | false => 1

theorem csb_dir_letter (c : ℝ) (b : Bool) :
    (Sob.cylinder c).dir (csbLetter b) = csbDir b := by
  cases b <;> rfl

/-- Every Boolean word of length `≤ m` is the direction list of a word of length `m`. -/
theorem csb_exists_idx (c : ℝ) : ∀ (m : ℕ) (u : List Bool), u.length ≤ m →
    ∃ α : Sob.Idx 2 m, (Sob.cylinder c).word α = u.map csbDir := by
  intro m
  induction m with
  | zero =>
    intro u hu
    cases u with
    | nil => exact ⟨Sob.Idx.zero, by simp⟩
    | cons b u' => simp at hu
  | succ m ih =>
    intro u hu
    cases u with
    | nil => exact ⟨Sob.Idx.zero, by simp⟩
    | cons b u' =>
      have hu' : u'.length ≤ m := by
        simp only [List.length_cons] at hu
        omega
      obtain ⟨α, hα⟩ := ih u' hu'
      refine ⟨Sob.Idx.cons (csbLetter b) α, ?_⟩
      rw [Sob.TestDomain.word_cons, hα, csb_dir_letter, List.map_cons]

/-! ### Components of vector fields -/

theorem csb_fderiv_comp_apply {g : ℝ × ℝ → Cyl.Vec2} {z : ℝ × ℝ} (hg : DifferentiableAt ℝ g z)
    (i : Fin 2) (v : ℝ × ℝ) :
    fderiv ℝ (fun y => g y i) z v = fderiv ℝ g z v i := by
  have hP : HasFDerivAt (fun y => (EuclideanSpace.proj i : Cyl.Vec2 →L[ℝ] ℝ) (g y))
      ((EuclideanSpace.proj i : Cyl.Vec2 →L[ℝ] ℝ).comp (fderiv ℝ g z)) z :=
    (EuclideanSpace.proj i : Cyl.Vec2 →L[ℝ] ℝ).hasFDerivAt.comp z hg.hasFDerivAt
  show fderiv ℝ (fun y => (EuclideanSpace.proj i : Cyl.Vec2 →L[ℝ] ℝ) (g y)) z v = _
  rw [hP.fderiv]
  rfl

theorem csb_differentiable_comp {g : ℝ × ℝ → Cyl.Vec2} (hg : Differentiable ℝ g) (i : Fin 2) :
    Differentiable ℝ (fun y => g y i) := fun z =>
  ((EuclideanSpace.proj i : Cyl.Vec2 →L[ℝ] ℝ).differentiableAt).comp z (hg z)

/-- The word derivatives of a component are the components of the classical derivatives. -/
theorem csb_derivWord_comp {f : ℝ × ℝ → Cyl.Vec2} (hf : ContDiff ℝ ∞ f) (i : Fin 2) :
    ∀ u : List Bool, UnforcedLeray.B0151.derivWord u (fun z => f z i) =
      fun z => Sob.iterD (u.map csbDir) f z i := by
  intro u
  induction u with
  | nil => rfl
  | cons b u ih =>
    funext z
    have hd : Differentiable ℝ (Sob.iterD (u.map csbDir) f) :=
      (Sob.contDiff_iterD hf _).differentiable (by simp)
    have hdc : Differentiable ℝ (fun y => Sob.iterD (u.map csbDir) f y i) :=
      csb_differentiable_comp hd i
    cases b with
    | true =>
      show UnforcedLeray.GaussianVortex.partialX
        (UnforcedLeray.B0151.derivWord u (fun z => f z i)) z = _
      rw [ih, UnforcedLeray.B0151.partialX_eq_fderiv hdc z, csb_fderiv_comp_apply (hd z) i]
      rfl
    | false =>
      show UnforcedLeray.GaussianVortex.partialY
        (UnforcedLeray.B0151.derivWord u (fun z => f z i)) z = _
      rw [ih, UnforcedLeray.B0151.partialY_eq_fderiv hdc z, csb_fderiv_comp_apply (hd z) i]
      rfl

theorem csb_enorm_apply_le (v : Cyl.Vec2) (i : Fin 2) : ‖v i‖ₑ ≤ ‖v‖ₑ :=
  PiLp.enorm_apply_le v i

/-! ### The real sup bound on the cylinder cell -/

/-- Along one word, the sup bound from `B0151.enorm_derivWord_le`, with the cell norms of the
word derivatives of length `≤ m + 2` transported to the centred cell. -/
theorem csb_sup_word {c : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c) {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hp : UnforcedLeray.B0151.IsPeriodicQ c h) {m : ℕ} {M : ENNReal} (hMt : M ≠ ⊤)
    (hM : ∀ u : List Bool, u.length ≤ m + 2 →
      eLpNorm (UnforcedLeray.B0151.derivWord u h) 2 (UnforcedLeray.Cyl.cellμ c) ≤ M)
    (w : List Bool) (hw : w.length ≤ m) (z : ℝ × ℝ) :
    ‖UnforcedLeray.B0151.derivWord w h z‖ₑ ≤ 3 * (M + M + M + M) := by
  have hmeas : ∀ u : List Bool, Measurable (UnforcedLeray.B0151.derivWord u h) := fun u =>
    (UnforcedLeray.B0151.contDiff_derivWord hh u).continuous.measurable
  have hcyc : ∀ u : List Bool,
      UnforcedLeray.Cyl.IsPeriodic c (UnforcedLeray.B0151.derivWord u h) :=
    fun u y => UnforcedLeray.B0151.periodic_derivWord hp u y.1 y.2
  have hmem : ∀ u : List Bool, u.length ≤ m + 2 →
      MemLp (UnforcedLeray.B0151.derivWord u h) 2 (UnforcedLeray.B0151.cellMeasure c) := by
    intro u hu
    have hL : MemLp (UnforcedLeray.B0151.derivWord u h) 2 (UnforcedLeray.Cyl.cellμ c) :=
      ⟨(hmeas u).aestronglyMeasurable, lt_of_le_of_lt (hM u hu) (lt_top_iff_ne_top.2 hMt)⟩
    exact UnforcedLeray.TrainB.memLp_b0151_of_cell hc (hmeas u) (hcyc u) hL
  have hbr : ∀ u : List Bool, u.length ≤ m + 2 →
      eLpNorm (UnforcedLeray.B0151.derivWord u h) 2 (UnforcedLeray.B0151.cellMeasure c) ≤ M := by
    intro u hu
    rw [UnforcedLeray.TrainB.eLpNorm_sq_b0151_eq_cyl hc (hmeas u) (hcyc u)]
    exact hM u hu
  have key := UnforcedLeray.B0151.enorm_derivWord_le hc1 hh hp w
    (hmem w (by omega)) (hmem (true :: w) (by simp only [List.length_cons]; omega))
    (hmem (false :: w) (by simp only [List.length_cons]; omega))
    (hmem (false :: true :: w) (by simp only [List.length_cons]; omega)) z
  refine key.trans (mul_le_mul_of_nonneg_left ?_ zero_le)
  exact add_le_add (add_le_add (add_le_add (hbr w (by omega))
    (hbr (true :: w) (by simp only [List.length_cons]; omega)))
    (hbr (false :: w) (by simp only [List.length_cons]; omega)))
    (hbr (false :: true :: w) (by simp only [List.length_cons]; omega))

/-- The real form of the sup bound: `|D_w h z| ≤ 12 N` when every cell norm is at most `N`. -/
theorem csb_sup_word_real {c : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c) {h : ℝ × ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hp : UnforcedLeray.B0151.IsPeriodicQ c h) {m : ℕ} {N : ℝ}
    (hN : 0 ≤ N)
    (hM : ∀ u : List Bool, u.length ≤ m + 2 →
      eLpNorm (UnforcedLeray.B0151.derivWord u h) 2 (UnforcedLeray.Cyl.cellμ c) ≤
        ENNReal.ofReal N)
    (w : List Bool) (hw : w.length ≤ m) (z : ℝ × ℝ) :
    |UnforcedLeray.B0151.derivWord w h z| ≤ 12 * N := by
  have h1 := csb_sup_word hc hc1 hh hp ENNReal.ofReal_ne_top hM w hw z
  have h2 : (3 : ENNReal) * (ENNReal.ofReal N + ENNReal.ofReal N + ENNReal.ofReal N +
      ENNReal.ofReal N) = ENNReal.ofReal (12 * N) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12), ENNReal.ofReal_ofNat]
    ring
  rw [h2, Real.enorm_eq_ofReal_abs] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num) hN)).1 h1

/-! ### The norm identification -/

/-- Each word component of an element of `W` is at most its norm. -/
theorem csb_deriv_le {c : ℝ} {m : ℕ} (ρ : Sob.Weight (ℝ × ℝ))
    (x : Sob.W (Sob.cylinder c) ρ ℝ Cyl.Vec2 m 2) (α : Sob.Idx 2 m) :
    ‖Sob.W.deriv (Sob.cylinder c) ρ ℝ Cyl.Vec2 m 2 α x‖ ≤ ‖x‖ := by
  have hsq : ‖Sob.W.deriv (Sob.cylinder c) ρ ℝ Cyl.Vec2 m 2 α x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [Sob.W.norm_sq x]
    exact Finset.single_le_sum (f := fun β : Sob.Idx 2 m =>
      ‖Sob.W.deriv (Sob.cylinder c) ρ ℝ Cyl.Vec2 m 2 β x‖ ^ 2)
      (fun β _ => sq_nonneg _) (Finset.mem_univ α)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- The cell `L²` norm of the component `i` of the classical word derivative `u` of a smooth
periodic field is at most `‖W.ofCylSmooth f‖`, for every word of length `≤ k + 3`. -/
theorem csb_comp_bound {c : ℝ} (hc : 0 < c) (k : ℕ) {f : ℝ × ℝ → Cyl.Vec2}
    (hf : Sob.IsCylSmooth c f) (i : Fin 2) (u : List Bool) (hu : u.length ≤ k + 3) :
    eLpNorm (UnforcedLeray.B0151.derivWord u (fun z => f z i)) 2
        (UnforcedLeray.Cyl.cellμ c) ≤
      ENNReal.ofReal ‖Sob.W.ofCylSmooth (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
        (F := Cyl.Vec2) (k := k + 3) (p := 2) hc f hf‖ := by
  obtain ⟨α, hα⟩ := csb_exists_idx c (k + 3) u hu
  have hμ : Sob.wμ (Sob.cylinder c).μ (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) =
      UnforcedLeray.Cyl.cellμ c :=
    UnforcedLeray.TrainB.vecH1_measure_eq_cell c
  set x := Sob.W.ofCylSmooth (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
    (F := Cyl.Vec2) (k := k + 3) (p := 2) hc f hf with hx
  set y := Sob.W.deriv (Sob.cylinder c) (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2
    (k + 3) 2 α x with hy
  have hnorm : ‖y‖ ≤ ‖x‖ := csb_deriv_le (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) x α
  have hae : Sob.iterD ((Sob.cylinder c).word α) f =ᵐ[UnforcedLeray.Cyl.cellμ c] ⇑y := by
    have h1 := Sob.W.deriv_ofCylSmooth (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := Cyl.Vec2) (k := k + 3) (p := 2) hc f hf α
    have key : ∀ ν : Measure (ℝ × ℝ),
        Sob.wμ (Sob.cylinder c).μ (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = ν →
          Sob.iterD ((Sob.cylinder c).word α) f =ᵐ[ν] ⇑y := by
      rintro ν rfl
      exact h1.symm
    exact key _ hμ
  have hcoord : eLpNorm (fun z => Sob.iterD ((Sob.cylinder c).word α) f z i) 2
      (UnforcedLeray.Cyl.cellμ c) ≤
      eLpNorm (Sob.iterD ((Sob.cylinder c).word α) f) 2 (UnforcedLeray.Cyl.cellμ c) :=
    eLpNorm_mono_enorm (fun z => csb_enorm_apply_le _ i)
  rw [csb_derivWord_comp hf.smooth i u, ← hα]
  refine hcoord.trans ?_
  rw [eLpNorm_congr_ae hae, ← hμ, ← Lp.enorm_def, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hnorm

/-! ### The Sobolev bound -/

theorem cylSmoothSobolevBound : CylSmoothSobolevBound := by
  unfold CylSmoothSobolevBound
  intro c hc hc1 k
  refine ⟨24 * 2 ^ (k + 1), fun f hf j hj z => ?_⟩
  have hsmooth : ContDiff ℝ ∞ f := hf.smooth
  have hci : ∀ i : Fin 2, ContDiff ℝ ∞ (fun y => f y i) := fun i =>
    (EuclideanSpace.proj i : Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp hsmooth
  have hper : ∀ i : Fin 2, UnforcedLeray.B0151.IsPeriodicQ c (fun y => f y i) := by
    intro i
    unfold UnforcedLeray.B0151.IsPeriodicQ
    intro q η
    show f (q + c, η) i = f (q, η) i
    have e : ((q + c, η) : ℝ × ℝ) = (q, η) + (c, 0) := by
      ext <;> simp
    rw [e, hf.periodic]
  set N := ‖Sob.W.ofCylSmooth (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
    (F := Cyl.Vec2) (k := k + 3) (p := 2) hc f hf‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  have hword : ∀ i : Fin 2, ∀ w : List Bool, w.length ≤ k + 1 → ∀ y : ℝ × ℝ,
      |UnforcedLeray.B0151.derivWord w (fun y' => f y' i) y| ≤ 12 * N := fun i w hw y =>
    csb_sup_word_real hc hc1 (hci i) (hper i) hN0
      (fun u hu => csb_comp_bound hc k hf i u (by omega)) w hw y
  have hiter : ∀ i : Fin 2, ‖iteratedFDeriv ℝ j (fun y => f y i) z‖ ≤ 2 ^ j * (12 * N) :=
    fun i => UnforcedLeray.Short.Spine.norm_iteratedFDeriv_le_of_derivWord (hci i) j z
      (fun w hw => hword i w (by omega) z)
  have heuc := UnforcedLeray.Short.Spine.norm_iteratedFDeriv_euclid2_le hsmooth j z
  have hpow : (2 : ℝ) ^ j ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) hj
  calc ‖iteratedFDeriv ℝ j f z‖
      ≤ ‖iteratedFDeriv ℝ j (fun y => f y 0) z‖ + ‖iteratedFDeriv ℝ j (fun y => f y 1) z‖ :=
        heuc
    _ ≤ 2 ^ j * (12 * N) + 2 ^ j * (12 * N) := add_le_add (hiter 0) (hiter 1)
    _ = 24 * 2 ^ j * N := by ring
    _ ≤ 24 * 2 ^ (k + 1) * N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) hN0

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.cylSmoothSobolevBound
