import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_2.Commute
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The fixed-age identity `SliceEq` (source 3511-3514, 3420-3426, 4610-4612)

Source of record: `the November 2 reference manuscript` (73 pages).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsCausalEnergySolution flatIntegrand IsFlatTest IsBiotSavart
  flowIntegrand trainVel flatDt flatLap flatGrad lapP)

namespace SliceEqAux

abbrev TT : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### Partial derivatives -/

theorem pd_comm (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ TT f) (j k : Fin 2) :
    B0579.pd j (B0579.pd k f) = B0579.pd k (B0579.pd j f) := by
  funext x
  have hs : IsSymmSndFDerivAt ℝ f x := (hf.contDiffAt).isSymmSndFDerivAt (by simp)
  have hdf : ContDiff ℝ TT (fderiv ℝ f) := hf.fderiv_right (m := TT) (by simp)
  have key : ∀ j : Fin 2, ∀ k : Fin 2,
      B0579.pd k (B0579.pd j f) x = fderiv ℝ (fderiv ℝ f) x (B0579.dir k) (B0579.dir j) := by
    intro j k
    unfold B0579.pd
    have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
      (hdf.differentiable (by simp)).differentiableAt
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [key, key]
  exact hs _ _

theorem pd_neg (f : ℝ × ℝ → ℝ) (j : Fin 2) :
    B0579.pd j (fun y => -f y) = fun y => -B0579.pd j f y := by
  funext x
  unfold B0579.pd
  rw [fderiv_fun_neg]
  simp

theorem pd_add {f g : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (j : Fin 2) :
    B0579.pd j (fun y => f y + g y) x = B0579.pd j f x + B0579.pd j g x := by
  unfold B0579.pd
  rw [fderiv_fun_add hf hg]
  simp

theorem pd_sub {f g : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (j : Fin 2) :
    B0579.pd j (fun y => f y - g y) x = B0579.pd j f x - B0579.pd j g x := by
  unfold B0579.pd
  rw [fderiv_fun_sub hf hg]
  simp

theorem pd_mul {f g : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (j : Fin 2) :
    B0579.pd j (fun y => f y * g y) x = B0579.pd j f x * g x + f x * B0579.pd j g x := by
  unfold B0579.pd
  rw [fderiv_fun_mul hf hg]
  simp
  ring

theorem pd0_eq_partialQ {φ : ℝ × ℝ → ℝ} (hφ : Differentiable ℝ φ) (z : ℝ × ℝ) :
    B0579.pd 0 φ z = UnforcedLeray.Cyl.partialQ φ z := by
  rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hφ]
  rfl

theorem pd1_eq_partialEta {φ : ℝ × ℝ → ℝ} (hφ : Differentiable ℝ φ) (z : ℝ × ℝ) :
    B0579.pd 1 φ z = UnforcedLeray.Cyl.partialEta φ z := by
  rw [UnforcedLeray.Cyl.partialEta_eq_fderiv hφ]
  rfl

/-! ### Smooth periodic factors and cylinder tests -/

/-- Smooth and `c`-periodic in `q` (no support condition). -/
def SmPer (c : ℝ) (a : ℝ × ℝ → ℝ) : Prop :=
  ContDiff ℝ TT a ∧ ∀ x : ℝ × ℝ, a (x.1 + c, x.2) = a x

theorem SmPer.pd {c : ℝ} {a : ℝ × ℝ → ℝ} (ha : SmPer c a) (j : Fin 2) :
    SmPer c (B0579.pd j a) := by
  refine ⟨((contDiff_infty_iff_fderiv.1 ha.1).2).clm_apply contDiff_const, fun x => ?_⟩
  have hfun : (fun y : ℝ × ℝ => a (y + ((c, 0) : ℝ × ℝ))) = a := by
    funext y
    have hy : y + ((c, 0) : ℝ × ℝ) = (y.1 + c, y.2) := by ext <;> simp
    rw [hy]
    exact ha.2 y
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := a) (x := x) ((c, 0) : ℝ × ℝ)
  rw [hfun] at h
  have hx : x + ((c, 0) : ℝ × ℝ) = (x.1 + c, x.2) := by ext <;> simp
  rw [hx] at h
  simp only [B0579.pd]
  rw [← h]

theorem SmPer.sub {c : ℝ} {a b : ℝ × ℝ → ℝ} (ha : SmPer c a) (hb : SmPer c b) :
    SmPer c (fun x => a x - b x) :=
  ⟨ha.1.sub hb.1, fun x => by simp only [ha.2 x, hb.2 x]⟩

theorem SmPer.of_cyl {c : ℝ} {a : ℝ × ℝ → ℝ} (ha : B0579.IsCylTest c a) : SmPer c a :=
  ⟨ha.smooth, ha.periodic⟩

theorem cyl_add {c : ℝ} {f g : ℝ × ℝ → ℝ} (hf : B0579.IsCylTest c f)
    (hg : B0579.IsCylTest c g) : B0579.IsCylTest c (fun x => f x + g x) where
  smooth := hf.smooth.add hg.smooth
  periodic x := by simp only [hf.periodic x, hg.periodic x]
  band := by
    obtain ⟨R1, h1⟩ := hf.band
    obtain ⟨R2, h2⟩ := hg.band
    refine ⟨max R1 R2, fun x hx => ?_⟩
    rw [h1 x (lt_of_le_of_lt (le_max_left _ _) hx), h2 x (lt_of_le_of_lt (le_max_right _ _) hx)]
    simp

theorem cyl_sub {c : ℝ} {f g : ℝ × ℝ → ℝ} (hf : B0579.IsCylTest c f)
    (hg : B0579.IsCylTest c g) : B0579.IsCylTest c (fun x => f x - g x) where
  smooth := hf.smooth.sub hg.smooth
  periodic x := by simp only [hf.periodic x, hg.periodic x]
  band := by
    obtain ⟨R1, h1⟩ := hf.band
    obtain ⟨R2, h2⟩ := hg.band
    refine ⟨max R1 R2, fun x hx => ?_⟩
    rw [h1 x (lt_of_le_of_lt (le_max_left _ _) hx), h2 x (lt_of_le_of_lt (le_max_right _ _) hx)]
    simp

theorem cyl_smul {c : ℝ} {a χ : ℝ × ℝ → ℝ} (ha : SmPer c a) (hχ : B0579.IsCylTest c χ) :
    B0579.IsCylTest c (fun x => a x * χ x) where
  smooth := ha.1.mul hχ.smooth
  periodic x := by simp only [ha.2 x, hχ.periodic x]
  band := by
    obtain ⟨R, hR⟩ := hχ.band
    exact ⟨R, fun x hx => by simp [hR x hx]⟩

/-! ### Integrability -/

theorem cyl_memLp {c : ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    MemLp ψ 2 (volume.restrict (B0579.cell c)) := by
  obtain ⟨R, hR⟩ := hψ.vanish
  exact B0579.memLp_cell_of_continuous hψ.continuous (B0579.isCompact_box c R) hR

theorem int_mul {c : ℝ} {u : ℝ × ℝ → ℂ} {ψ : ℝ × ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (B0579.cell c))) (hψ : B0579.IsCylTest c ψ) :
    Integrable (fun x => u x * (ψ x : ℂ)) (volume.restrict (B0579.cell c)) := by
  have h2 : MemLp (fun x => (ψ x : ℂ)) 2 (volume.restrict (B0579.cell c)) :=
    (cyl_memLp hψ).ofReal
  exact hu.integrable_mul h2

/-! ### The train at a fixed age -/

section Train

variable {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)

theorem v_smper {s : ℝ} (hs : 0 < s) (i : Fin 2) : SmPer c (fun x => tr.v s x i) :=
  ⟨contDiff_euclidean.1 (UnforcedLeray.B0238.contDiff_Vc tr hs.le) i,
    fun x => by
      show (tr.v s (x.1 + c, x.2)) i = (tr.v s x) i
      rw [tr.isTrain.periodic_v s hs.le x]⟩

theorem Ec_eq {s : ℝ} (hs : 0 < s) :
    UnforcedLeray.B0238.Ec tr s = fun z => B0579.pd 0 (fun x => tr.v s x 1) z -
      B0579.pd 1 (fun x => tr.v s x 0) z := by
  funext z
  have d0 : Differentiable ℝ (fun x => tr.v s x 0) := (v_smper tr hs 0).1.differentiable (by simp)
  have d1 : Differentiable ℝ (fun x => tr.v s x 1) := (v_smper tr hs 1).1.differentiable (by simp)
  simp only [UnforcedLeray.B0238.Ec, UnforcedLeray.Cyl.curl]
  rw [pd0_eq_partialQ d1, pd1_eq_partialEta d0]

theorem div_eq {s : ℝ} (hs : 0 < s) (z : ℝ × ℝ) :
    B0579.pd 0 (fun x => tr.v s x 0) z + B0579.pd 1 (fun x => tr.v s x 1) z = 0 := by
  have d0 : Differentiable ℝ (fun x => tr.v s x 0) := (v_smper tr hs 0).1.differentiable (by simp)
  have d1 : Differentiable ℝ (fun x => tr.v s x 1) := (v_smper tr hs 1).1.differentiable (by simp)
  have h := tr.isTrain.solenoidal s hs.le z
  simp only [UnforcedLeray.Cyl.divergence] at h
  rw [pd0_eq_partialQ d0, pd1_eq_partialEta d1]
  exact h

theorem E_smper {s : ℝ} (hs : 0 < s) : SmPer c (UnforcedLeray.B0238.Ec tr s) := by
  rw [Ec_eq tr hs]
  exact ((v_smper tr hs 1).pd 0).sub ((v_smper tr hs 0).pd 1)

/-- `w = v·∇ζ`. -/
def wF (s : ℝ) (ζs : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun y => tr.v s y 0 * B0579.pd 0 ζs y + tr.v s y 1 * B0579.pd 1 ζs y

/-- `Π = v₁∂_qζ - v₀∂_ηζ - Eζ`. -/
def PiF (s : ℝ) (ζs : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun y => tr.v s y 1 * B0579.pd 0 ζs y - tr.v s y 0 * B0579.pd 1 ζs y -
    UnforcedLeray.B0238.Ec tr s y * ζs y

theorem wF_cyl {s : ℝ} (hs : 0 < s) {ζs : ℝ × ℝ → ℝ} (hζ : B0579.IsCylTest c ζs) :
    B0579.IsCylTest c (wF tr s ζs) :=
  cyl_add (cyl_smul (v_smper tr hs 0) (hζ.pd 0)) (cyl_smul (v_smper tr hs 1) (hζ.pd 1))

theorem PiF_cyl {s : ℝ} (hs : 0 < s) {ζs : ℝ × ℝ → ℝ} (hζ : B0579.IsCylTest c ζs) :
    B0579.IsCylTest c (PiF tr s ζs) :=
  cyl_sub (cyl_sub (cyl_smul (v_smper tr hs 1) (hζ.pd 0)) (cyl_smul (v_smper tr hs 0) (hζ.pd 1)))
    (cyl_smul (E_smper tr hs) hζ)

theorem pd_wF {s : ℝ} (hs : 0 < s) {ζs : ℝ × ℝ → ℝ} (hζ : B0579.IsCylTest c ζs) (j : Fin 2)
    (x : ℝ × ℝ) :
    B0579.pd j (wF tr s ζs) x =
      B0579.pd j (fun y => tr.v s y 0) x * B0579.pd 0 ζs x +
        tr.v s x 0 * B0579.pd j (B0579.pd 0 ζs) x +
      (B0579.pd j (fun y => tr.v s y 1) x * B0579.pd 1 ζs x +
        tr.v s x 1 * B0579.pd j (B0579.pd 1 ζs) x) := by
  have dv0 : Differentiable ℝ (fun y => tr.v s y 0) :=
    (v_smper tr hs 0).1.differentiable (by simp)
  have dv1 : Differentiable ℝ (fun y => tr.v s y 1) :=
    (v_smper tr hs 1).1.differentiable (by simp)
  have dz0 := (hζ.pd 0).differentiable
  have dz1 := (hζ.pd 1).differentiable
  have h0 : DifferentiableAt ℝ (fun y => tr.v s y 0 * B0579.pd 0 ζs y) x :=
    (dv0.mul dz0).differentiableAt
  have h1 : DifferentiableAt ℝ (fun y => tr.v s y 1 * B0579.pd 1 ζs y) x :=
    (dv1.mul dz1).differentiableAt
  unfold wF
  rw [pd_add h0 h1,
    pd_mul dv0.differentiableAt dz0.differentiableAt,
    pd_mul dv1.differentiableAt dz1.differentiableAt]

theorem pd_PiF {s : ℝ} (hs : 0 < s) {ζs : ℝ × ℝ → ℝ} (hζ : B0579.IsCylTest c ζs) (j : Fin 2)
    (x : ℝ × ℝ) :
    B0579.pd j (PiF tr s ζs) x =
      B0579.pd j (fun y => tr.v s y 1) x * B0579.pd 0 ζs x +
        tr.v s x 1 * B0579.pd j (B0579.pd 0 ζs) x -
      (B0579.pd j (fun y => tr.v s y 0) x * B0579.pd 1 ζs x +
        tr.v s x 0 * B0579.pd j (B0579.pd 1 ζs) x) -
      (B0579.pd j (UnforcedLeray.B0238.Ec tr s) x * ζs x +
        UnforcedLeray.B0238.Ec tr s x * B0579.pd j ζs x) := by
  have dv0 : Differentiable ℝ (fun y => tr.v s y 0) :=
    (v_smper tr hs 0).1.differentiable (by simp)
  have dv1 : Differentiable ℝ (fun y => tr.v s y 1) :=
    (v_smper tr hs 1).1.differentiable (by simp)
  have dE : Differentiable ℝ (UnforcedLeray.B0238.Ec tr s) :=
    (E_smper tr hs).1.differentiable (by simp)
  have dz := hζ.differentiable
  have dz0 := (hζ.pd 0).differentiable
  have dz1 := (hζ.pd 1).differentiable
  have h0 : DifferentiableAt ℝ (fun y => tr.v s y 1 * B0579.pd 0 ζs y) x :=
    (dv1.mul dz0).differentiableAt
  have h1 : DifferentiableAt ℝ (fun y => tr.v s y 0 * B0579.pd 1 ζs y) x :=
    (dv0.mul dz1).differentiableAt
  have h2 : DifferentiableAt ℝ (fun y => UnforcedLeray.B0238.Ec tr s y * ζs y) x :=
    (dE.mul dz).differentiableAt
  have h3 : DifferentiableAt ℝ
      (fun y => tr.v s y 1 * B0579.pd 0 ζs y - tr.v s y 0 * B0579.pd 1 ζs y) x :=
    (h0.sub h1)
  unfold PiF
  rw [pd_sub h3 h2,
    pd_sub h0 h1,
    pd_mul dv1.differentiableAt dz0.differentiableAt,
    pd_mul dv0.differentiableAt dz1.differentiableAt,
    pd_mul dE.differentiableAt dz.differentiableAt]

end Train

/-! ### The pointwise identity -/

theorem streamField_zero (ζ : ℝ → ℝ × ℝ → ℝ) (s : ℝ) :
    (fun y => streamField ζ s y 0) = fun y => -B0579.pd 1 (ζ s) y := by
  funext y; simp [streamField]

theorem streamField_one (ζ : ℝ → ℝ × ℝ → ℝ) (s : ℝ) :
    (fun y => streamField ζ s y 1) = B0579.pd 0 (ζ s) := by
  funext y; simp [streamField]

theorem forced_pointwise {ν c μ : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (f b : Chart → Fin 2 → ℂ) (ζ : ℝ → ℝ × ℝ → ℝ) (hζ : IsStreamTest c ζ) {s : ℝ}
    (hs : 0 < s) (x : ℝ × ℝ) :
    forcedIntegrand ν (μ : ℂ) (trainVel tr) f b (streamField ζ) (s, x) =
      (b (s, x) 0 * (B0579.pd 1 (fun x => deriv (fun t => ζ t x) s) x : ℂ) -
        b (s, x) 1 * (B0579.pd 0 (fun x => deriv (fun t => ζ t x) s) x : ℂ)) +
      (-((μ : ℂ) / (s : ℂ))) * (b (s, x) 0 * (B0579.pd 1 (ζ s) x : ℂ) -
        b (s, x) 1 * (B0579.pd 0 (ζ s) x : ℂ)) +
      (ν : ℂ) * (b (s, x) 0 * (B0579.pd 1 (lapP (ζ s)) x : ℂ) -
        b (s, x) 1 * (B0579.pd 0 (lapP (ζ s)) x : ℂ)) +
      (b (s, x) 0 * (B0579.pd 1 (wF tr s (ζ s)) x : ℂ) -
        b (s, x) 1 * (B0579.pd 0 (wF tr s (ζ s)) x : ℂ)) -
      (b (s, x) 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr s) x : ℂ) +
        b (s, x) 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr s) x : ℂ)) * (ζ s x : ℂ) -
      (b (s, x) 0 * (B0579.pd 0 (PiF tr s (ζ s)) x : ℂ) +
        b (s, x) 1 * (B0579.pd 1 (PiF tr s (ζ s)) x : ℂ)) +
      (f (s, x) 0 * (B0579.pd 1 (ζ s) x : ℂ) - f (s, x) 1 * (B0579.pd 0 (ζ s) x : ℂ)) := by
  obtain ⟨-, -, hdt, hlap⟩ := sliceCommute c ζ hζ
  have hcyl : B0579.IsCylTest c (ζ s) := hζ.2.1 s
  have hsm : ContDiff ℝ TT (ζ s) := hcyl.smooth
  have hv : ∀ i, trainVel tr s x i = tr.v s x i := fun i => by simp [trainVel, hs.le]
  have g0 : ∀ j, flatGrad (streamField ζ) s x 0 j = -B0579.pd j (B0579.pd 1 (ζ s)) x := by
    intro j
    unfold flatGrad
    rw [streamField_zero, pd_neg]
  have g1 : ∀ j, flatGrad (streamField ζ) s x 1 j = B0579.pd j (B0579.pd 0 (ζ s)) x := by
    intro j
    unfold flatGrad
    rw [streamField_one]
  have hcomm := pd_comm (ζ s) hsm 1 0
  have hw0 := pd_wF tr hs hcyl 0 x
  have hw1 := pd_wF tr hs hcyl 1 x
  have hP0 := pd_PiF tr hs hcyl 0 x
  have hP1 := pd_PiF tr hs hcyl 1 x
  have hdiv := div_eq tr hs x
  have hcurl : UnforcedLeray.B0238.Ec tr s x = B0579.pd 0 (fun x => tr.v s x 1) x -
      B0579.pd 1 (fun x => tr.v s x 0) x := by rw [Ec_eq tr hs]
  have hdivC : ((B0579.pd 0 (fun x => tr.v s x 0) x : ℝ) : ℂ) +
      ((B0579.pd 1 (fun x => tr.v s x 1) x : ℝ) : ℂ) = 0 := by exact_mod_cast hdiv
  have hcurlC : ((UnforcedLeray.B0238.Ec tr s x : ℝ) : ℂ) =
      ((B0579.pd 0 (fun x => tr.v s x 1) x : ℝ) : ℂ) -
      ((B0579.pd 1 (fun x => tr.v s x 0) x : ℝ) : ℂ) := by exact_mod_cast hcurl
  unfold forcedIntegrand flatIntegrand
  simp only [Fin.sum_univ_two]
  rw [hdt, hdt, hlap, hlap, g0, g0, g1, g1, hv, hv, hw0, hw1, hP0, hP1]
  simp only [streamField]
  rw [hcomm]
  simp
  linear_combination
    (-(b (s, x) 0 * ((B0579.pd 0 (ζ s) x : ℝ) : ℂ) + b (s, x) 1 * ((B0579.pd 1 (ζ s) x : ℝ) : ℂ))) *
        hcurlC +
      (-(b (s, x) 0 * ((B0579.pd 1 (ζ s) x : ℝ) : ℂ) - b (s, x) 1 * ((B0579.pd 0 (ζ s) x : ℝ) : ℂ))) *
        hdivC


/-! ### Assembly -/

/-- The curl pairing integrand `b₀∂_ηψ - b₁∂_qψ`. -/
def seC (b0 b1 : ℝ × ℝ → ℂ) (ψ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℂ :=
  b0 x * (B0579.pd 1 ψ x : ℂ) - b1 x * (B0579.pd 0 ψ x : ℂ)

/-- The gradient pairing integrand `b₀∂_qψ + b₁∂_ηψ`. -/
def seD (b0 b1 : ℝ × ℝ → ℂ) (ψ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℂ :=
  b0 x * (B0579.pd 0 ψ x : ℂ) + b1 x * (B0579.pd 1 ψ x : ℂ)

/-- Linear combination of seven integrable functions. -/
theorem integral_comb7 {α : Type*} [MeasurableSpace α] {m : Measure α} {A1 A2 A3 A4 A5 A6 A7 : α → ℂ}
    (k2 k3 : ℂ) (h1 : Integrable A1 m) (h2 : Integrable A2 m) (h3 : Integrable A3 m)
    (h4 : Integrable A4 m) (h5 : Integrable A5 m) (h6 : Integrable A6 m) (h7 : Integrable A7 m) :
    Integrable (fun x => A1 x + k2 * A2 x + k3 * A3 x + A4 x - A5 x - A6 x + A7 x) m ∧
      ∫ x, (A1 x + k2 * A2 x + k3 * A3 x + A4 x - A5 x - A6 x + A7 x) ∂m =
        ∫ x, A1 x ∂m + k2 * ∫ x, A2 x ∂m + k3 * ∫ x, A3 x ∂m + ∫ x, A4 x ∂m - ∫ x, A5 x ∂m -
          ∫ x, A6 x ∂m + ∫ x, A7 x ∂m := by
  have e1 : Integrable (fun x => A1 x + k2 * A2 x) m := h1.add (h2.const_mul k2)
  have e2 : Integrable (fun x => A1 x + k2 * A2 x + k3 * A3 x) m := e1.add (h3.const_mul k3)
  have e3 : Integrable (fun x => A1 x + k2 * A2 x + k3 * A3 x + A4 x) m := e2.add h4
  have e4 : Integrable (fun x => A1 x + k2 * A2 x + k3 * A3 x + A4 x - A5 x) m := e3.sub h5
  have e5 : Integrable (fun x => A1 x + k2 * A2 x + k3 * A3 x + A4 x - A5 x - A6 x) m := e4.sub h6
  refine ⟨e5.add h7, ?_⟩
  rw [integral_add e5 h7, integral_sub e4 h6, integral_sub e3 h5, integral_add e2 h4,
    integral_add e1 (h3.const_mul k3), integral_add h1 (h2.const_mul k2), integral_const_mul,
    integral_const_mul]

/-- Linear combination of three integrable functions. -/
theorem integral_comb3 {α : Type*} [MeasurableSpace α] {m : Measure α} {A1 A2 A3 : α → ℂ}
    (k : ℂ) (h1 : Integrable A1 m) (h2 : Integrable A2 m) (h3 : Integrable A3 m) :
    ∫ x, (k * A1 x + A2 x - A3 x) ∂m = k * ∫ x, A1 x ∂m + ∫ x, A2 x ∂m - ∫ x, A3 x ∂m := by
  have e1 : Integrable (fun x => k * A1 x) m := h1.const_mul k
  have e2 : Integrable (fun x => k * A1 x + A2 x) m := e1.add h2
  rw [integral_sub e2 h3, integral_add e1 h2, integral_const_mul]

end SliceEqAux

open SliceEqAux in
theorem sliceEq : SliceEq := by
  intro ν c μ tr ω g b G f H ζ hζ s hs hSL
  obtain ⟨hν, hc, hBUC, hE, hBS, hf, hcurl, hid, hOmInt⟩ := H
  obtain ⟨hZ, hL, -, -⟩ := sliceCommute c ζ hζ
  have hcyl : B0579.IsCylTest c (ζ s) := hζ.2.1 s
  have hZc : B0579.IsCylTest c (fun x => deriv (fun t => ζ t x) s) := hZ.2.1 s
  have hLc : B0579.IsCylTest c (lapP (ζ s)) := hL.2.1 s
  have hwc := wF_cyl tr hs hcyl
  have hPc := PiF_cyl tr hs hcyl
  have hb : ∀ i, MemLp (fun x => b (s, x) i) 2 (volume.restrict (B0579.cell c)) :=
    fun i => (hSL i).1
  have hfL : ∀ i, MemLp (fun x => f (s, x) i) 2 (volume.restrict (B0579.cell c)) :=
    fun i => (hSL i).2
  set b0 : ℝ × ℝ → ℂ := fun x => b (s, x) 0 with hb0
  set b1 : ℝ × ℝ → ℂ := fun x => b (s, x) 1 with hb1
  -- the curl pairings
  have hCint : ∀ ψ, B0579.IsCylTest c ψ →
      Integrable (seC b0 b1 ψ) (volume.restrict (B0579.cell c)) := fun ψ hψ =>
    (int_mul (hb 0) (hψ.pd 1)).sub (int_mul (hb 1) (hψ.pd 0))
  have hCeq : ∀ ψ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, seC b0 b1 ψ x = ∫ x in B0579.cell c, ω s x * (ψ x : ℂ) :=
    fun ψ hψ => ((hBS s hs).2.2 ψ hψ).symm
  have hDint : ∀ ψ, B0579.IsCylTest c ψ →
      Integrable (seD b0 b1 ψ) (volume.restrict (B0579.cell c)) := fun ψ hψ =>
    (int_mul (hb 0) (hψ.pd 0)).add (int_mul (hb 1) (hψ.pd 1))
  have hDzero : ∫ x in B0579.cell c, seD b0 b1 (PiF tr s (ζ s)) x = 0 :=
    hE.divFree s hs _ hPc
  -- the force term
  have hTint : Integrable (fun x => f (s, x) 0 * (B0579.pd 1 (ζ s) x : ℂ) -
      f (s, x) 1 * (B0579.pd 0 (ζ s) x : ℂ)) (volume.restrict (B0579.cell c)) :=
    (int_mul (hfL 0) (hcyl.pd 1)).sub (int_mul (hfL 1) (hcyl.pd 0))
  have hTeq : ∫ x in B0579.cell c, (f (s, x) 0 * (B0579.pd 1 (ζ s) x : ℂ) -
      f (s, x) 1 * (B0579.pd 0 (ζ s) x : ℂ)) = ∫ x in B0579.cell c, g s x * (ζ s x : ℂ) :=
    (hcurl s hs (ζ s) hcyl).symm
  -- the `∇E` term
  have hEint : Integrable (fun x => seD b0 b1 (UnforcedLeray.B0238.Ec tr s) x * (ζ s x : ℂ))
      (volume.restrict (B0579.cell c)) := by
    have h0 := int_mul (hb 0) (cyl_smul ((E_smper tr hs).pd 0) hcyl)
    have h1 := int_mul (hb 1) (cyl_smul ((E_smper tr hs).pd 1) hcyl)
    refine (h0.add h1).congr (Eventually.of_forall fun x => ?_)
    simp only [seD, hb0, hb1, Pi.add_apply]
    push_cast
    ring
  -- the flow integrand
  have hflow : ∀ x, flowIntegrand tr (ω s) (fun x => b (s, x)) s (ζ s) x =
      (ν : ℂ) * (ω s x * (lapP (ζ s) x : ℂ)) + ω s x * (wF tr s (ζ s) x : ℂ) -
        seD b0 b1 (UnforcedLeray.B0238.Ec tr s) x * (ζ s x : ℂ) := by
    intro x
    simp only [flowIntegrand, wF, seD, hb0, hb1]
    push_cast
    ring
  have hOL := hOmInt s hs _ hLc
  have hOw := hOmInt s hs _ hwc
  have hflowInt : Integrable (flowIntegrand tr (ω s) (fun x => b (s, x)) s (ζ s))
      (volume.restrict (B0579.cell c)) := by
    have : flowIntegrand tr (ω s) (fun x => b (s, x)) s (ζ s) = fun x =>
        (ν : ℂ) * (ω s x * (lapP (ζ s) x : ℂ)) + ω s x * (wF tr s (ζ s) x : ℂ) -
          seD b0 b1 (UnforcedLeray.B0238.Ec tr s) x * (ζ s x : ℂ) := funext hflow
    rw [this]
    exact ((hOL.const_mul (ν : ℂ)).add hOw).sub hEint
  have hflowEq : ∫ x in B0579.cell c, flowIntegrand tr (ω s) (fun x => b (s, x)) s (ζ s) x =
      (ν : ℂ) * (∫ x in B0579.cell c, ω s x * (lapP (ζ s) x : ℂ)) +
        (∫ x in B0579.cell c, ω s x * (wF tr s (ζ s) x : ℂ)) -
        (∫ x in B0579.cell c, seD b0 b1 (UnforcedLeray.B0238.Ec tr s) x * (ζ s x : ℂ)) := by
    simp_rw [hflow]
    exact integral_comb3 (ν : ℂ) hOL hOw hEint
  -- the forced integrand
  have hkey : ∀ x, forcedIntegrand ν (μ : ℂ) (trainVel tr) f b (streamField ζ) (s, x) =
      seC b0 b1 (fun x => deriv (fun t => ζ t x) s) x +
        (-((μ : ℂ) / (s : ℂ))) * seC b0 b1 (ζ s) x +
        (ν : ℂ) * seC b0 b1 (lapP (ζ s)) x + seC b0 b1 (wF tr s (ζ s)) x -
        seD b0 b1 (UnforcedLeray.B0238.Ec tr s) x * (ζ s x : ℂ) -
        seD b0 b1 (PiF tr s (ζ s)) x +
        (f (s, x) 0 * (B0579.pd 1 (ζ s) x : ℂ) - f (s, x) 1 * (B0579.pd 0 (ζ s) x : ℂ)) := by
    intro x
    rw [forced_pointwise tr f b ζ hζ hs x]
    rfl
  have hFeq : (fun x => forcedIntegrand ν (μ : ℂ) (trainVel tr) f b (streamField ζ) (s, x)) =
      fun x => seC b0 b1 (fun x => deriv (fun t => ζ t x) s) x +
        (-((μ : ℂ) / (s : ℂ))) * seC b0 b1 (ζ s) x +
        (ν : ℂ) * seC b0 b1 (lapP (ζ s)) x + seC b0 b1 (wF tr s (ζ s)) x -
        seD b0 b1 (UnforcedLeray.B0238.Ec tr s) x * (ζ s x : ℂ) -
        seD b0 b1 (PiF tr s (ζ s)) x +
        (f (s, x) 0 * (B0579.pd 1 (ζ s) x : ℂ) - f (s, x) 1 * (B0579.pd 0 (ζ s) x : ℂ)) :=
    funext hkey
  have i1 := hCint _ hZc
  have i2 := hCint _ hcyl
  have i3 := hCint _ hLc
  have i4 := hCint _ hwc
  have i6 := hDint _ hPc
  have hc7 := integral_comb7 (m := volume.restrict (B0579.cell c)) (-((μ : ℂ) / (s : ℂ))) (ν : ℂ)
    i1 i2 i3 i4 hEint i6 hTint
  rw [hFeq]
  refine ⟨hc7.1, ?_⟩
  rw [hc7.2, hCeq _ hZc, hCeq _ hcyl, hCeq _ hLc, hCeq _ hwc, hDzero, hTeq]
  unfold streamSlice
  rw [hflowEq]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
