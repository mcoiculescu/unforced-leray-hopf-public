import UnforcedLeray.Short.PartIIa.Sub.R08
import UnforcedLeray.Lib.Train.Profile
import UnforcedLeray.Lib.Gaussian.Periodization
import UnforcedLeray.Lib.Axisymmetric.Cylindrical

/-!
# Part II-a, task `PartII-a:R08`: the inlet has zero pointwise divergence (`InletDivZero`)

Source of record: `the November 2 reference manuscript`, line 1210 (stream form
`u_r = -r⁻¹ ∂_z 𝒫`, `u_z = r⁻¹ ∂_r 𝒫`) and lines 1330-1336 (the `t = 0` inlet).

Outline.
* `trainDatum c` is the periodization of the Gaussian stream, hence `C^∞` on `ℝ²`
  (`Gaussian.contDiff_periodize`), so `𝒫 = inletStream c R` is `C^∞` on `{r > 0}`.
* Off the axis, `inletRaw c R = Axi.liftMer b` for the meridional profile
  `b = (-ρ⁻¹ ∂_z𝒫, ρ⁻¹ ∂_ρ𝒫)`, and `Axi.divergence_liftMer` gives
  `∂_ρ b_r + b_r/ρ + ∂_z b_z = ρ⁻¹ (∂_z∂_ρ𝒫 - ∂_ρ∂_z𝒫) = 0` (symmetry of second derivatives).
* A `C¹` extension `a` agrees with `inletRaw` on the open set `axisᶜ`, so its divergence vanishes
  there.
* On the axis (`x ≠ 0`) the divergence of `a` is continuous on `{x ≠ 0}` and vanishes on the
  punctured line `t ↦ x + t e₀`, hence vanishes at `x`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

namespace InletDivZeroAux

/-! ### Smoothness of the Gaussian train datum -/

theorem psi0_translate_bound (k : ℕ) : ∃ C : ℝ, ∀ z : ℝ × ℝ,
    ‖iteratedFDeriv ℝ k UnforcedLeray.Train.psi0 z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  obtain ⟨A, hA, hb⟩ := UnforcedLeray.Train.norm_iteratedFDeriv_psi0_le k
  obtain ⟨K, hK, hk⟩ := UnforcedLeray.Train.exp_neg_sq_div_eight_le_rpow
  refine ⟨A * K, fun z => (hb z).trans ?_⟩
  have h1 : Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤ Real.exp (-z.1 ^ 2 / 8) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg z.2])
  calc A * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)
      ≤ A * (K * (1 + |z.1|) ^ (-(2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (h1.trans (hk z.1)) hA
    _ = A * K * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring

theorem trainDatum_eq_periodize (c : ℝ) (z : ℝ × ℝ) :
    trainDatum c z.1 z.2 = Gaussian.periodize c UnforcedLeray.Train.psi0 z := by
  obtain ⟨q, η⟩ := z
  unfold trainDatum Gaussian.periodize
  congr 1
  funext n
  simp only [UnforcedLeray.Train.psi0, UnforcedLeray.Train.gauss0]
  congr 2
  ring

theorem contDiff_trainDatum {c : ℝ} (hc : c ≠ 0) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => trainDatum c z.1 z.2) := by
  have h := Gaussian.contDiff_periodize (N := ⊤) (s := 2) (by norm_num) hc
    UnforcedLeray.Train.contDiff_psi0 (fun k _ => psi0_translate_bound k)
  have e : (fun z : ℝ × ℝ => trainDatum c z.1 z.2) =
      Gaussian.periodize c UnforcedLeray.Train.psi0 :=
    funext fun z => trainDatum_eq_periodize c z
  rw [e]
  exact h

/-- The datum stream `𝒫(r, z)` as a function on `ℝ × ℝ`. -/
def streamPair (c R : ℝ) (z : ℝ × ℝ) : ℝ := inletStream c R z.1 z.2

theorem contDiffAt_streamPair {c R : ℝ} (hc : c ≠ 0) (hR : R ≠ 0) {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContDiffAt ℝ 2 (streamPair c R) p := by
  have hq : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => R * Real.log (z.1 / R)) p :=
    contDiffAt_const.mul ((Real.contDiffAt_log.2 (div_ne_zero hp.ne' hR)).comp p
      (contDiffAt_fst.div_const R))
  have hη : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => R * z.2 / z.1) p :=
    (contDiffAt_const.mul contDiffAt_snd).div contDiffAt_fst hp.ne'
  have hT : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => trainDatum c z.1 z.2)
      (R * Real.log (p.1 / R), R * p.2 / p.1) :=
    (contDiff_trainDatum hc).contDiffAt
  have hcomp := hT.comp p (hq.prodMk hη)
  have h := contDiffAt_fst.mul hcomp
  exact h.of_le (WithTop.coe_le_coe.mpr le_top)

/-! ### Derivatives in the meridional directions -/

theorem deriv_snd_eq_fderiv' {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : DifferentiableAt ℝ f p) :
    deriv (fun t => f (p.1, t)) p.2 = fderiv ℝ f p (0, 1) := by
  have h1 : HasDerivAt (fun t : ℝ => ((p.1, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact (hf.hasFDerivAt.comp_hasDerivAt p.2 h1).deriv

theorem deriv_fst_eq_fderiv' {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : DifferentiableAt ℝ f p) :
    deriv (fun t => f (t, p.2)) p.1 = fderiv ℝ f p (1, 0) := by
  have h1 : HasDerivAt (fun t : ℝ => ((t, p.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  exact (hf.hasFDerivAt.comp_hasDerivAt p.1 h1).deriv

/-- The first coordinate projection, as a Fréchet derivative. -/
theorem hasFDerivAt_fst_pair (p : ℝ × ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
  hasFDerivAt_fst

/-- Second-derivative bookkeeping: the partial derivative `v` of `fderiv P` is differentiable and
its derivative in direction `w` is the second derivative evaluated at `(w, v)`. -/
theorem fderiv_apply_spec {P : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hP : ContDiffAt ℝ 2 P p) (v : ℝ × ℝ) :
    DifferentiableAt ℝ (fun q => fderiv ℝ P q v) p ∧
      ∀ w : ℝ × ℝ, fderiv ℝ (fun q => fderiv ℝ P q v) p w = fderiv ℝ (fderiv ℝ P) p w v := by
  have hD : ContDiffAt ℝ 1 (fderiv ℝ P) p := hP.fderiv_right (m := 1) (by norm_num)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ P) p := hD.differentiableAt (by norm_num)
  have h : HasFDerivAt (fun q => fderiv ℝ P q v)
      ((fderiv ℝ P p).comp 0 + (fderiv ℝ (fderiv ℝ P) p).flip v) p :=
    hdiff.hasFDerivAt.clm_apply (hasFDerivAt_const v p)
  refine ⟨h.differentiableAt, fun w => ?_⟩
  rw [h.fderiv]
  simp

/-- A vector-valued map differentiates componentwise. -/
theorem fderiv_apply_proj {g : ℝ × ℝ → Axi.Merid} {p : ℝ × ℝ} (hg : DifferentiableAt ℝ g p)
    (j : Fin 2) (v : ℝ × ℝ) :
    fderiv ℝ g p v j = fderiv ℝ (fun q => g q j) p v := by
  have h : HasFDerivAt (fun q => g q j)
      ((EuclideanSpace.proj j : Axi.Merid →L[ℝ] ℝ).comp (fderiv ℝ g p)) p :=
    (EuclideanSpace.proj j : Axi.Merid →L[ℝ] ℝ).hasFDerivAt.comp p hg.hasFDerivAt
  rw [h.fderiv]
  simp

/-! ### The meridional profile of the inlet -/

/-- The unit vector `e_r`-slot of the meridional plane, `(1, 0)`. -/
def e0M : Axi.Merid := EuclideanSpace.single 0 1

/-- The unit vector `e_z`-slot of the meridional plane, `(0, 1)`. -/
def e1M : Axi.Merid := EuclideanSpace.single 1 1

/-- The meridional profile `(b_r, b_z) = (-ρ⁻¹ ∂_z𝒫, ρ⁻¹ ∂_ρ𝒫)` of the stream `𝒫`, written with
`fderiv`. -/
def profileB (P : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : Axi.Merid :=
  (-(q.1)⁻¹ * fderiv ℝ P q (0, 1)) • e0M + ((q.1)⁻¹ * fderiv ℝ P q (1, 0)) • e1M

theorem profileB_apply_zero (P : ℝ × ℝ → ℝ) (q : ℝ × ℝ) :
    profileB P q 0 = -(q.1)⁻¹ * fderiv ℝ P q (0, 1) := by
  simp [profileB, e0M, e1M, EuclideanSpace.single_apply]

theorem profileB_apply_one (P : ℝ × ℝ → ℝ) (q : ℝ × ℝ) :
    profileB P q 1 = (q.1)⁻¹ * fderiv ℝ P q (1, 0) := by
  simp [profileB, e0M, e1M, EuclideanSpace.single_apply]

theorem profileB_differentiableAt {P : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hP : ContDiffAt ℝ 2 P p)
    (hp : p.1 ≠ 0) : DifferentiableAt ℝ (profileB P) p := by
  have hD0 : DifferentiableAt ℝ (fun q => fderiv ℝ P q (0, 1)) p :=
    (fderiv_apply_spec hP (0, 1)).1
  have hD1 : DifferentiableAt ℝ (fun q => fderiv ℝ P q (1, 0)) p :=
    (fderiv_apply_spec hP (1, 0)).1
  have hi : DifferentiableAt ℝ (fun q : ℝ × ℝ => (q.1)⁻¹) p := differentiableAt_fst.inv hp
  have hF0 : DifferentiableAt ℝ (fun q : ℝ × ℝ => -(q.1)⁻¹ * fderiv ℝ P q (0, 1)) p :=
    hi.neg.mul hD0
  have hF1 : DifferentiableAt ℝ (fun q : ℝ × ℝ => (q.1)⁻¹ * fderiv ℝ P q (1, 0)) p :=
    hi.mul hD1
  exact (hF0.smul_const e0M).add (hF1.smul_const e1M)

/-- The meridional lift of the profile is the inlet, off the axis. -/
theorem liftMer_profileB_eq (c R : ℝ) {x : Space} (hx : x ∉ Axi.axis)
    (hd : DifferentiableAt ℝ (streamPair c R) (Axi.mer x)) :
    Axi.liftMer (profileB (streamPair c R)) x = inletRaw c R x := by
  have hA : deriv (fun z => inletStream c R (Axi.ϱ x) z) (x 2) =
      fderiv ℝ (streamPair c R) (Axi.mer x) (0, 1) :=
    deriv_snd_eq_fderiv' hd
  have hB : deriv (fun r => inletStream c R r (x 2)) (Axi.ϱ x) =
      fderiv ℝ (streamPair c R) (Axi.mer x) (1, 0) :=
    deriv_fst_eq_fderiv' hd
  have h0 : profileB (streamPair c R) (Axi.mer x) 0 =
      -(Axi.ϱ x)⁻¹ * deriv (fun z => inletStream c R (Axi.ϱ x) z) (x 2) := by
    rw [hA]
    exact profileB_apply_zero _ _
  have h1 : profileB (streamPair c R) (Axi.mer x) 1 =
      (Axi.ϱ x)⁻¹ * deriv (fun r => inletStream c R r (x 2)) (Axi.ϱ x) := by
    rw [hB]
    exact profileB_apply_one _ _
  unfold Axi.liftMer inletRaw
  rw [h0, h1]
  simp only [one_div]

/-- The second-derivative identity: the divergence of the meridional profile vanishes at a point
off the axis where the stream is `C²`. -/
theorem profileB_div_zero {P : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hP : ContDiffAt ℝ 2 P p)
    (hp : p.1 ≠ 0) :
    Axi.dρ (profileB P) p 0 + profileB P p 0 / p.1 + Axi.dz (profileB P) p 1 = 0 := by
  have hsym : IsSymmSndFDerivAt ℝ P p := hP.isSymmSndFDerivAt (by simp)
  have hdiff : DifferentiableAt ℝ (profileB P) p := profileB_differentiableAt hP hp
  have hD0d : DifferentiableAt ℝ (fun q => fderiv ℝ P q (0, 1)) p :=
    (fderiv_apply_spec hP (0, 1)).1
  have hD1d : DifferentiableAt ℝ (fun q => fderiv ℝ P q (1, 0)) p :=
    (fderiv_apply_spec hP (1, 0)).1
  have e0 : (fun q : ℝ × ℝ => profileB P q 0) =
      fun q : ℝ × ℝ => -(q.1)⁻¹ * fderiv ℝ P q (0, 1) :=
    funext (profileB_apply_zero P)
  have e1 : (fun q : ℝ × ℝ => profileB P q 1) =
      fun q : ℝ × ℝ => (q.1)⁻¹ * fderiv ℝ P q (1, 0) :=
    funext (profileB_apply_one P)
  have hdρ : Axi.dρ (profileB P) p 0 =
      fderiv ℝ (fun q : ℝ × ℝ => -(q.1)⁻¹ * fderiv ℝ P q (0, 1)) p (1, 0) := by
    rw [← e0]
    exact fderiv_apply_proj hdiff 0 (1, 0)
  have hdz : Axi.dz (profileB P) p 1 =
      fderiv ℝ (fun q : ℝ × ℝ => (q.1)⁻¹ * fderiv ℝ P q (1, 0)) p (0, 1) := by
    rw [← e1]
    exact fderiv_apply_proj hdiff 1 (0, 1)
  have hF0 : HasFDerivAt (fun q : ℝ × ℝ => -(q.1)⁻¹ * fderiv ℝ P q (0, 1))
      ((-(p.1)⁻¹) • fderiv ℝ (fun q => fderiv ℝ P q (0, 1)) p +
        fderiv ℝ P p (0, 1) • ((p.1 ^ 2)⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ)) p := by
    have hi : HasFDerivAt (fun q : ℝ × ℝ => -(q.1)⁻¹)
        ((p.1 ^ 2)⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
      have h := ((hasDerivAt_inv hp).comp_hasFDerivAt p (hasFDerivAt_fst_pair p)).neg
      rw [neg_smul, neg_neg] at h
      exact h
    exact hi.mul hD0d.hasFDerivAt
  have hF1 : HasFDerivAt (fun q : ℝ × ℝ => (q.1)⁻¹ * fderiv ℝ P q (1, 0))
      ((p.1)⁻¹ • fderiv ℝ (fun q => fderiv ℝ P q (1, 0)) p +
        fderiv ℝ P p (1, 0) • ((-(p.1 ^ 2)⁻¹) • ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
    ((hasDerivAt_inv hp).comp_hasFDerivAt p (hasFDerivAt_fst_pair p)).mul hD1d.hasFDerivAt
  have hval0 : profileB P p 0 = -(p.1)⁻¹ * fderiv ℝ P p (0, 1) := profileB_apply_zero P p
  have hS : fderiv ℝ (fun q => fderiv ℝ P q (0, 1)) p (1, 0) =
      fderiv ℝ (fderiv ℝ P) p (1, 0) (0, 1) := (fderiv_apply_spec hP (0, 1)).2 (1, 0)
  have hT : fderiv ℝ (fun q => fderiv ℝ P q (1, 0)) p (0, 1) =
      fderiv ℝ (fderiv ℝ P) p (0, 1) (1, 0) := (fderiv_apply_spec hP (1, 0)).2 (0, 1)
  have hsymm : fderiv ℝ (fderiv ℝ P) p (1, 0) (0, 1) =
      fderiv ℝ (fderiv ℝ P) p (0, 1) (1, 0) := hsym (1, 0) (0, 1)
  rw [hdρ, hdz, hval0, hF0.fderiv, hF1.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.coe_fst']
  linear_combination (-(p.1)⁻¹) * hS + (p.1)⁻¹ * hT + (-(p.1)⁻¹) * hsymm

/-- The divergence of the inlet vanishes off the axis. -/
theorem divergence_inletRaw_off_axis {c R : ℝ} (hc : c ≠ 0) (hR : R ≠ 0) {x : Space}
    (hx : x ∉ Axi.axis) : Axi.divergence (inletRaw c R) x = 0 := by
  have hP : ∀ y : Space, y ∉ Axi.axis → ContDiffAt ℝ 2 (streamPair c R) (Axi.mer y) :=
    fun y hy => contDiffAt_streamPair (p := Axi.mer y) hc hR (Axi.ϱ_pos hy)
  have hev : Axi.liftMer (profileB (streamPair c R)) =ᶠ[𝓝 x] inletRaw c R := by
    filter_upwards [Axi.isOpen_compl_axis.mem_nhds (Set.mem_compl hx)] with y hy
    exact liftMer_profileB_eq c R hy ((hP y hy).differentiableAt (by norm_num))
  have hdiv : Axi.divergence (inletRaw c R) x =
      Axi.divergence (Axi.liftMer (profileB (streamPair c R))) x := by
    unfold Axi.divergence
    rw [hev.fderiv_eq]
  have hp : (Axi.mer x).1 ≠ 0 := Axi.ϱ_ne_zero hx
  rw [hdiv, Axi.divergence_liftMer hx (profileB_differentiableAt (hP x hx) hp)]
  exact profileB_div_zero (hP x hx) hp

end InletDivZeroAux

open InletDivZeroAux in
/-- The sum `∑ᵢ ∂ᵢ aᵢ` of a field, the quantity in `InletDivZero`. -/
def divSum (a : Space → Space) (y : Space) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ a y (coordinateVector i) i

open InletDivZeroAux in
/-- **Task `PartII-a:R08`, target `InletDivZero`.** A `C¹` extension of `inletRaw` on `{x ≠ 0}` has
zero divergence on `{x ≠ 0}`. -/
theorem inletDivZero_proof : InletDivZero := by
  intro c R hc hR a ha haeq x hx
  have hc0 : c ≠ 0 := hc.ne'
  have hR0 : R ≠ 0 := by
    intro h
    rw [h] at hR
    norm_num at hR
  -- Off the axis: `a` agrees with `inletRaw` on a neighbourhood, so the divergences agree.
  have hoff : ∀ y : Space, y ∉ Axi.axis → divSum a y = 0 := by
    intro y hy
    have hae : a =ᶠ[𝓝 y] inletRaw c R := by
      filter_upwards [Axi.isOpen_compl_axis.mem_nhds (Set.mem_compl hy)] with z hz using
        haeq z hz
    have hdv : divSum a y = Axi.divergence (inletRaw c R) y := by
      unfold divSum Axi.divergence
      rw [hae.fderiv_eq]
    rw [hdv]
    exact divergence_inletRaw_off_axis hc0 hR0 hy
  show divSum a x = 0
  by_cases hxa : x ∈ Axi.axis
  · -- On the axis: continuity of the divergence and a punctured line through `x`.
    have hU : IsOpen {y : Space | y ≠ 0} := isOpen_ne
    have hfd : ContinuousOn (fderiv ℝ a) {y : Space | y ≠ 0} :=
      ha.continuousOn_fderiv_of_isOpen hU le_rfl
    have hfdc : ContinuousAt (fderiv ℝ a) x := hfd.continuousAt (hU.mem_nhds hx)
    have hcomp : ∀ i : Fin 3, ContinuousAt (fun y => fderiv ℝ a y (coordinateVector i) i) x := by
      intro i
      have h1 : ContinuousAt (fun y => fderiv ℝ a y (coordinateVector i)) x :=
        hfdc.clm_apply continuousAt_const
      exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).continuousAt.comp h1
    have hDc : ContinuousAt (divSum a) x := by
      unfold divSum
      simp only [Fin.sum_univ_three]
      exact ((hcomp 0).add (hcomp 1)).add (hcomp 2)
    have hx0 : x 0 = 0 := by
      have h := hxa
      simp only [Axi.axis, Set.mem_setOf_eq] at h
      exact h.1
    have hline : ∀ t : ℝ, t ≠ 0 → divSum a (x + t • coordinateVector (0 : Fin 3)) = 0 := by
      intro t ht
      apply hoff
      intro hmem
      have h0 : (x + t • coordinateVector (0 : Fin 3)) 0 = 0 := by
        have h := hmem
        simp only [Axi.axis, Set.mem_setOf_eq] at h
        exact h.1
      simp [Axi.coordinateVector_apply, hx0] at h0
      exact ht h0
    have hγ : Continuous (fun t : ℝ => x + t • coordinateVector (0 : Fin 3)) := by
      fun_prop
    have hD' : ContinuousAt (divSum a) (x + (0 : ℝ) • coordinateVector (0 : Fin 3)) := by
      simpa using hDc
    have hcont : ContinuousAt (fun t : ℝ => divSum a (x + t • coordinateVector (0 : Fin 3))) 0 :=
      ContinuousAt.comp (f := fun t : ℝ => x + t • coordinateVector (0 : Fin 3)) (x := (0 : ℝ))
        hD' hγ.continuousAt
    have hlim1 : Tendsto (fun t : ℝ => divSum a (x + t • coordinateVector (0 : Fin 3)))
        (𝓝[≠] (0 : ℝ)) (𝓝 (divSum a (x + (0 : ℝ) • coordinateVector (0 : Fin 3)))) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hlim1' : Tendsto (fun t : ℝ => divSum a (x + t • coordinateVector (0 : Fin 3)))
        (𝓝[≠] (0 : ℝ)) (𝓝 (divSum a x)) := by
      simpa using hlim1
    have hlim0 : Tendsto (fun t : ℝ => divSum a (x + t • coordinateVector (0 : Fin 3)))
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hline t ht).symm
    exact tendsto_nhds_unique hlim1' hlim0
  · exact hoff x hxa

end UnforcedLeray.Short.PartIIa
