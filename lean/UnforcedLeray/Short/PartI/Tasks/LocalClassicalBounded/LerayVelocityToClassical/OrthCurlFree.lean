import UnforcedLeray.Short.PartI.Sub.T02_1_5
import UnforcedLeray.Lib.CylinderB.Tests
import UnforcedLeray.Lib.Cylinder.IBP
import UnforcedLeray.Lib.Sobolev.Cylinder
import UnforcedLeray.Lib.Train.Ops

/-!
# Part I, task `PartI:T02/1/5/3`: the curl-free part of the Leray orthogonality

Source of record: `the November 2 reference manuscript`, lines 261-288 (Leray
pressure).  Target: `OrthCurlFree` (`Short/PartI/Sub/T02_1_5.lean`).

Mathematics.  Let `g` be smooth, `c`-periodic and `L²(cell)`-orthogonal to the admissible solenoidal
fields.  For a cylinder test `χ` the field `φ = (-∂_η χ, ∂_q χ)` is admissible (smooth, periodic,
divergence free by the symmetry of mixed partials, zero for `|η|` large).  Integration by parts on
the cell (`Cyl.integral_cell_partialQ_mul`, `Cyl.integral_cell_partialEta_mul`) turns the
orthogonality into `∫_cell χ (∂_q g₁ - ∂_η g₀) = 0` for all cylinder tests `χ`.  A bump-function
argument on the open strip (using `Sob.exists_isCylTest_eq`) gives the vanishing of the continuous
function `h = ∂_q g₁ - ∂_η g₀` on the strip, and periodicity in `q` extends it to the plane.

The proof is complete: no placeholder steps and no native decision procedures.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec toVecL)
open UnforcedLeray.Cyl (Plane)

/-- The `q`-derivative of a negated function. -/
theorem orthCurl_partialQ_neg (f : Plane → ℝ) (hf : Differentiable ℝ f) (w : Plane) :
    Cyl.partialQ (fun v => -(f v)) w = -Cyl.partialQ f w := by
  have hd : Differentiable ℝ (fun v => -(f v)) := fun v => (hf v).neg
  rw [Cyl.partialQ_eq_fderiv hd, Cyl.partialQ_eq_fderiv hf]
  rw [show (fun v => -(f v)) = -f from rfl, fderiv_neg]
  simp

/-- Mixed partial derivatives of a cylinder test commute. -/
theorem orthCurl_mixed {c : ℝ} {χ : Plane → ℝ} (hχ : Sob.IsCylTest c χ) (w : Plane) :
    Cyl.partialQ (Cyl.partialEta χ) w = Cyl.partialEta (Cyl.partialQ χ) w := by
  have hη : Sob.IsCylTest c (Cyl.partialEta χ) := Cyl.isCylTest_partialEta hχ
  have hq : Sob.IsCylTest c (Cyl.partialQ χ) := Cyl.isCylTest_partialQ hχ
  have hsymm : IsSymmSndFDerivAt ℝ χ w := hχ.smooth.contDiffAt.isSymmSndFDerivAt (by simp)
  have hFD : DifferentiableAt ℝ (fderiv ℝ χ) w :=
    ((hχ.smooth.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) w
  have key : ∀ v u : Plane,
      fderiv ℝ (fun x => fderiv ℝ χ x v) w u = fderiv ℝ (fderiv ℝ χ) w u v := by
    intro v u
    rw [fderiv_clm_apply hFD (differentiableAt_const v)]
    simp
  have e1 : Cyl.partialEta χ = fun x => fderiv ℝ χ x (0, 1) :=
    funext (Cyl.partialEta_eq_fderiv hχ.differentiable)
  have e2 : Cyl.partialQ χ = fun x => fderiv ℝ χ x (1, 0) :=
    funext (Cyl.partialQ_eq_fderiv hχ.differentiable)
  rw [Cyl.partialQ_eq_fderiv hη.differentiable, Cyl.partialEta_eq_fderiv hq.differentiable, e1, e2,
    key, key]
  exact hsymm (1, 0) (0, 1)

/-- A continuous `h` with `∫_cell χ h = 0` for all cylinder tests has no positive value in the
open strip. -/
theorem orthCurl_noPosOnStrip {c : ℝ} (hc : 0 < c) {h : Plane → ℝ} (hcont : Continuous h)
    (hint : ∀ χ : Plane → ℝ, Sob.IsCylTest c χ → ∫ z in Cyl.cell c, χ z * h z = 0)
    (v0 : Plane) (hv0 : v0.1 ∈ Ioo (-(c / 2)) (c / 2)) (hpos0 : 0 < h v0) : False := by
  have hOpen : IsOpen ((Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)) ∩ {w : Plane | 0 < h w}) :=
    (isOpen_Ioo.prod isOpen_univ).inter (isOpen_lt continuous_const hcont)
  have hv0W : v0 ∈ (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)) ∩ {w : Plane | 0 < h w} :=
    ⟨⟨hv0, mem_univ _⟩, hpos0⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hOpen v0 hv0W
  let ψ : ContDiffBump v0 :=
    { rIn := r / 4, rOut := r / 2, rIn_pos := by linarith, rIn_lt_rOut := by linarith }
  have hrOut : ψ.rOut = r / 2 := rfl
  have hψout : ∀ x : Plane, x ∉ Metric.ball v0 r → ψ x = 0 := by
    intro x hx
    apply ContDiffBump.zero_of_le_dist
    rw [Metric.mem_ball, not_lt] at hx
    rw [hrOut]
    linarith
  have hψc : HasCompactSupport (⇑ψ) := ψ.hasCompactSupport
  have hψs : ContDiff ℝ ∞ (⇑ψ) := ψ.contDiff
  have hlt : ψ.rOut < r := by
    rw [hrOut]
    linarith
  have hψsub : tsupport (⇑ψ) ⊆ Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ) := by
    rw [ψ.tsupport_eq]
    exact (Metric.closedBall_subset_ball hlt).trans (hball.trans fun x hx => hx.1)
  obtain ⟨Φ, hΦ, hΦψ⟩ := Sob.exists_isCylTest_eq hc hψs hψc hψsub
  have hcellEq : Cyl.cell c = Sob.cylCell c := by
    unfold Cyl.cell Sob.cylCell
    rw [neg_div]
  have hΦint : ∫ z in Sob.cylCell c, Φ z * h z = 0 := by
    rw [← hcellEq]
    exact hint Φ hΦ
  have hEq : ∫ z in Sob.cylCell c, Φ z * h z = ∫ z in Sob.cylCell c, ψ z * h z :=
    setIntegral_congr_fun (Sob.measurableSet_cylCell c) (fun x hx => by simp only [hΦψ x hx])
  have hψint : ∫ z in Sob.cylCell c, ψ z * h z = ∫ z, ψ z * h z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hxb : x ∉ Metric.ball v0 r := fun hxb =>
      hx ⟨Ioo_subset_Ico_self (hball hxb).1.1, mem_univ _⟩
    show ψ x * h x = 0
    rw [hψout x hxb, zero_mul]
  have hpos_int : 0 < ∫ z, ψ z * h z := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := v0)
      (hψs.continuous.mul hcont) hψc.mul_right ?_ ?_
    · intro x
      show (0 : ℝ) ≤ ψ x * h x
      by_cases hx : x ∈ Metric.ball v0 r
      · exact mul_nonneg ψ.nonneg (le_of_lt (hball hx).2)
      · rw [hψout x hx, zero_mul]
    · have hmem : v0 ∈ Metric.closedBall v0 ψ.rIn :=
        Metric.mem_closedBall_self (le_of_lt ψ.rIn_pos)
      show ψ v0 * h v0 ≠ 0
      rw [ψ.one_of_mem_closedBall hmem, one_mul]
      exact hpos0.ne'
  linarith [hΦint, hEq, hψint, hpos_int]

/-- Fundamental lemma on the open strip: `∫_cell χ h = 0` for all cylinder tests `χ` forces
`h = 0` on `Ioo (-(c/2)) (c/2) × ℝ`, for continuous `h`. -/
theorem orthCurl_zeroOnStrip {c : ℝ} (hc : 0 < c) {h : Plane → ℝ} (hcont : Continuous h)
    (hint : ∀ χ : Plane → ℝ, Sob.IsCylTest c χ → ∫ z in Cyl.cell c, χ z * h z = 0) :
    ∀ v : Plane, v.1 ∈ Ioo (-(c / 2)) (c / 2) → h v = 0 := by
  intro v hv
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hint' : ∀ χ : Plane → ℝ, Sob.IsCylTest c χ → ∫ z in Cyl.cell c, χ z * (-h z) = 0 := by
      intro χ hχ
      simp only [mul_neg, integral_neg, hint χ hχ, neg_zero]
    exact orthCurl_noPosOnStrip hc hcont.neg hint' v hv (by show 0 < -h v; linarith)
  · exact orthCurl_noPosOnStrip hc hcont hint v hv hgt

/-- A continuous `c`-periodic (in `q`) function vanishing on the strip vanishes everywhere. -/
theorem orthCurl_zeroOfPeriodic {c : ℝ} (hc : 0 < c) {h : Plane → ℝ} (hcont : Continuous h)
    (hper : ∀ v : Plane, h (v.1 + c, v.2) = h v)
    (hstrip : ∀ v : Plane, v.1 ∈ Ioo (-(c / 2)) (c / 2) → h v = 0) : ∀ v : Plane, h v = 0 := by
  intro v
  have hZ : IsClosed {w : Plane | h w = 0} := isClosed_eq hcont continuous_const
  have hcl : closure (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)) ⊆ {w : Plane | h w = 0} := by
    apply closure_minimal _ hZ
    intro w hw
    exact hstrip w hw.1
  have hp : Function.Periodic (fun q : ℝ => h (q, v.2)) c := fun q => hper (q, v.2)
  obtain ⟨y, hy, hyv⟩ := hp.exists_mem_Ico hc v.1 (-(c / 2))
  have hyc : y ∈ Icc (-(c / 2)) (c / 2) := ⟨hy.1, by linarith [hy.2]⟩
  have hne : -(c / 2) ≠ c / 2 := by
    intro e
    linarith
  have hmem : (y, v.2) ∈ closure (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)) := by
    rw [closure_prod_eq, closure_Ioo hne, closure_univ]
    exact ⟨hyc, mem_univ _⟩
  have h1 : h (y, v.2) = 0 := hcl hmem
  have h2 : h (v.1, v.2) = h (y, v.2) := hyv
  show h (v.1, v.2) = 0
  rw [h2]
  exact h1

/-- **Leaf 3** (curl-free part of the Leray orthogonality). -/
theorem orthCurlFree : OrthCurlFree := by
  unfold OrthCurlFree
  intro c g hc hg hper horth z
  have hg0 : ContDiff ℝ ∞ (fun w => g w 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hg
  have hg1 : ContDiff ℝ ∞ (fun w => g w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hg
  have hg0d : Differentiable ℝ (fun w => g w 0) := hg0.differentiable (by simp)
  have hg1d : Differentiable ℝ (fun w => g w 1) := hg1.differentiable (by simp)
  have hg0c : Continuous (fun w => g w 0) := hg0.continuous
  have hg1c : Continuous (fun w => g w 1) := hg1.continuous
  have hq1 : Continuous (Cyl.partialQ (fun w => g w 1)) := by
    rw [show Cyl.partialQ (fun w => g w 1) = fun x => fderiv ℝ (fun w => g w 1) x (1, 0) from
      funext (Cyl.partialQ_eq_fderiv hg1d)]
    exact (hg1.continuous_fderiv (by simp)).clm_apply continuous_const
  have he0 : Continuous (Cyl.partialEta (fun w => g w 0)) := by
    rw [show Cyl.partialEta (fun w => g w 0) = fun x => fderiv ℝ (fun w => g w 0) x (0, 1) from
      funext (Cyl.partialEta_eq_fderiv hg0d)]
    exact (hg0.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgp1 : Cyl.IsPeriodic c (fun w => g w 1) := fun v => by
    show g (v.1 + c, v.2) 1 = g v 1
    rw [hper v]
  have hgp0 : Cyl.IsPeriodic c (fun w => g w 0) := fun v => by
    show g (v.1 + c, v.2) 0 = g v 0
    rw [hper v]
  -- the integrated identity for every cylinder test
  have hkey : ∀ χ : Plane → ℝ, Sob.IsCylTest c χ →
      ∫ w in Cyl.cell c, χ w * (Cyl.partialQ (fun u => g u 1) w
        - Cyl.partialEta (fun u => g u 0) w) = 0 := by
    intro χ hχ
    have hη : Sob.IsCylTest c (Cyl.partialEta χ) := Cyl.isCylTest_partialEta hχ
    have hq : Sob.IsCylTest c (Cyl.partialQ χ) := Cyl.isCylTest_partialQ hχ
    have hφs : ContDiff ℝ ∞ (fun w : Plane => toVec (-(Cyl.partialEta χ w), Cyl.partialQ χ w)) :=
      toVecL.contDiff.comp (hη.smooth.neg.prodMk hq.smooth)
    have hφp : Cyl.IsPeriodic c
        (fun w : Plane => toVec (-(Cyl.partialEta χ w), Cyl.partialQ χ w)) := by
      intro w
      show toVec (-(Cyl.partialEta χ (w.1 + c, w.2)), Cyl.partialQ χ (w.1 + c, w.2))
        = toVec (-(Cyl.partialEta χ w), Cyl.partialQ χ w)
      rw [hη.isPeriodic w, hq.isPeriodic w]
    have hφsupp : ∃ R : ℝ, ∀ w : Plane, R < |w.2| →
        toVec (-(Cyl.partialEta χ w), Cyl.partialQ χ w) = 0 := by
      obtain ⟨R1, hR1⟩ := hη.bounded
      obtain ⟨R2, hR2⟩ := hq.bounded
      refine ⟨max R1 R2, fun w hw => ?_⟩
      rw [hR1 w (lt_of_le_of_lt (le_max_left _ _) hw),
        hR2 w (lt_of_le_of_lt (le_max_right _ _) hw), neg_zero]
      exact map_zero toVecL
    have hdiv : ∀ w : Plane,
        Cyl.divergence (fun v : Plane => toVec (-(Cyl.partialEta χ v), Cyl.partialQ χ v)) w = 0 := by
      intro w
      unfold Cyl.divergence
      simp only [UnforcedLeray.Train.toVec_zero, UnforcedLeray.Train.toVec_one]
      rw [orthCurl_partialQ_neg (Cyl.partialEta χ) hη.differentiable w, orthCurl_mixed hχ w]
      ring
    have hinner : ∀ v : Plane,
        inner ℝ (g v) (toVec (-(Cyl.partialEta χ v), Cyl.partialQ χ v))
          = Cyl.partialQ χ v * g v 1 - Cyl.partialEta χ v * g v 0 := by
      intro v
      simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
        UnforcedLeray.Train.toVec_zero, UnforcedLeray.Train.toVec_one]
      ring
    have hOrth := horth (fun v : Plane => toVec (-(Cyl.partialEta χ v), Cyl.partialQ χ v))
      hφs hφp hdiv hφsupp
    simp only [hinner] at hOrth
    have hsplit : ∫ z in Cyl.cell c, (Cyl.partialQ χ z * g z 1 - Cyl.partialEta χ z * g z 0)
        = (∫ z in Cyl.cell c, Cyl.partialQ χ z * g z 1)
          - (∫ z in Cyl.cell c, Cyl.partialEta χ z * g z 0) :=
      integral_sub (hq.integrableOn_mul hg1c) (hη.integrableOn_mul hg0c)
    have hIq : ∫ z in Cyl.cell c, Cyl.partialQ χ z * g z 1
        = -∫ z in Cyl.cell c, χ z * Cyl.partialQ (fun u => g u 1) z :=
      Cyl.integral_cell_partialQ_mul hc hχ.differentiable hg1d hχ.isPeriodic hgp1
        (hq.integrableOn_mul hg1c) (hχ.integrableOn_mul hq1)
    have hIe : ∫ z in Cyl.cell c, Cyl.partialEta χ z * g z 0
        = -∫ z in Cyl.cell c, χ z * Cyl.partialEta (fun u => g u 0) z :=
      Cyl.integral_cell_partialEta_mul hχ.differentiable hg0d (hχ.integrableOn_mul hg0c)
        (hη.integrableOn_mul hg0c) (hχ.integrableOn_mul he0)
    have hsub : ∫ z in Cyl.cell c, χ z * (Cyl.partialQ (fun u => g u 1) z
          - Cyl.partialEta (fun u => g u 0) z)
        = (∫ z in Cyl.cell c, χ z * Cyl.partialQ (fun u => g u 1) z)
          - (∫ z in Cyl.cell c, χ z * Cyl.partialEta (fun u => g u 0) z) := by
      rw [← integral_sub (hχ.integrableOn_mul hq1) (hχ.integrableOn_mul he0)]
      congr 1
      funext z
      ring
    rw [hsub]
    rw [hsplit] at hOrth
    linarith [hIq, hIe, hOrth]
  have hcont : Continuous
      (fun w => Cyl.partialQ (fun u => g u 1) w - Cyl.partialEta (fun u => g u 0) w) :=
    hq1.sub he0
  have hperh : ∀ v : Plane,
      Cyl.partialQ (fun u => g u 1) (v.1 + c, v.2)
          - Cyl.partialEta (fun u => g u 0) (v.1 + c, v.2)
        = Cyl.partialQ (fun u => g u 1) v - Cyl.partialEta (fun u => g u 0) v := by
    intro v
    rw [hgp1.partialQ v, hgp0.partialEta v]
  have hstrip := orthCurl_zeroOnStrip hc hcont hkey
  have hall := orthCurl_zeroOfPeriodic hc hcont hperh hstrip
  exact sub_eq_zero.mp (hall z)

end UnforcedLeray.Short.PartI
