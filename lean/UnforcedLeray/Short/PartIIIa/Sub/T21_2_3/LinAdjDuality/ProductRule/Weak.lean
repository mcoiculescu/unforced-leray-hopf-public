import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_5
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.RateSplit

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace LadPRWeakAux

lemma pdCx_lin {A B : ℝ × ℝ → ℂ} (k : Fin 2) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (c : ℂ) : pdCx k (fun y => A y + B y * c) = fun y => pdCx k A y + pdCx k B y * c := by
  funext y
  have hBc : ContDiff ℝ ∞ (fun y => B y * c) := hB.mul contDiff_const
  rw [RateSplitAux.pdCx_add k (hA.differentiable (by simp) y) (hBc.differentiable (by simp) y)]
  congr 1
  have h0 : pdCx k (fun _ : ℝ × ℝ => c) y = 0 := by simp [pdCx]
  have h1 := RateSplitAux.pdCx_mul k (f := B) (g := fun _ : ℝ × ℝ => c)
    (hB.differentiable (by simp) y) (differentiableAt_const c)
  simp only [h0, mul_zero, add_zero] at h1
  exact h1

lemma ladLapCx_lin {A B : ℝ × ℝ → ℂ} (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (c : ℂ)
    (x : ℝ × ℝ) :
    ladLapCx (fun y => A y + B y * c) x = ladLapCx A x + ladLapCx B x * c := by
  unfold ladLapCx
  rw [pdCx_lin 0 hA hB c, pdCx_lin 1 hA hB c]
  rw [pdCx_lin 0 (RateSplitAux.contDiff_pdCx hA 0) (RateSplitAux.contDiff_pdCx hB 0) c,
    pdCx_lin 1 (RateSplitAux.contDiff_pdCx hA 1) (RateSplitAux.contDiff_pdCx hB 1) c]
  dsimp only
  ring

lemma ladTransport_lin {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (ρ : ℝ)
    {A B : ℝ × ℝ → ℂ} (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (cc : ℂ) (x : ℝ × ℝ) :
    ladTransport tr ρ (fun y => A y + B y * cc) x =
      ladTransport tr ρ A x + ladTransport tr ρ B x * cc := by
  unfold ladTransport
  rw [pdCx_lin 0 hA hB cc, pdCx_lin 1 hA hB cc]
  dsimp only
  ring

lemma pdCx_ofReal_fun {a : ℝ × ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (k : Fin 2) :
    pdCx k (fun y => (a y : ℂ)) = fun y => ((B0579.pd k a y : ℝ) : ℂ) := by
  funext y
  exact RateSplitAux.pdCx_ofReal k (ha.differentiable (by simp) y)

lemma ladLapCx_ofReal {c : ℝ} {a : ℝ × ℝ → ℝ} (ha : B0579.IsCylTest c a) (x : ℝ × ℝ) :
    ladLapCx (fun y => (a y : ℂ)) x = ((lapP a x : ℝ) : ℂ) := by
  unfold ladLapCx lapP
  rw [pdCx_ofReal_fun ha.smooth 0, pdCx_ofReal_fun ha.smooth 1]
  rw [pdCx_ofReal_fun (ha.pd 0).smooth 0, pdCx_ofReal_fun (ha.pd 1).smooth 1]
  dsimp only
  push_cast
  ring

lemma ladTransport_ofReal {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (ρ : ℝ)
    {a : ℝ × ℝ → ℝ} (ha : B0579.IsCylTest c a) (x : ℝ × ℝ) :
    ladTransport tr ρ (fun y => (a y : ℂ)) x =
      ((tr.v ρ x 0 * B0579.pd 0 a x + tr.v ρ x 1 * B0579.pd 1 a x : ℝ) : ℂ) := by
  unfold ladTransport
  rw [pdCx_ofReal_fun ha.smooth 0, pdCx_ofReal_fun ha.smooth 1]
  dsimp only
  push_cast
  ring

/-- Pointwise: the complex flow integrand against `a + i b` splits into the real ones. -/
lemma ladFlow_split {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (om : ℝ × ℝ → ℂ)
    (u : ℝ × ℝ → Fin 2 → ℂ) (ρ : ℝ) {a b : ℝ × ℝ → ℝ} (ha : B0579.IsCylTest c a)
    (hb : B0579.IsCylTest c b) (x : ℝ × ℝ) :
    ladFlowCx tr om u ρ (fun y => (a y : ℂ) + (b y : ℂ) * Complex.I) x =
      flowIntegrand tr om u ρ a x + flowIntegrand tr om u ρ b x * Complex.I := by
  have hA : ContDiff ℝ ∞ (fun y => (a y : ℂ)) := RateSplitAux.contDiff_ofReal ha.smooth
  have hB : ContDiff ℝ ∞ (fun y => (b y : ℂ)) := RateSplitAux.contDiff_ofReal hb.smooth
  unfold ladFlowCx
  rw [ladLapCx_lin hA hB Complex.I x, ladTransport_lin tr ρ hA hB Complex.I x,
    ladLapCx_ofReal ha x, ladLapCx_ofReal hb x, ladTransport_ofReal tr ρ ha x,
    ladTransport_ofReal tr ρ hb x]
  unfold flowIntegrand ladForce
  push_cast
  ring

/-- Integrability of `w · a` on the cell for `w ∈ X_{m,c}` and a real cylinder test `a`. -/
lemma integ_w {c m : ℝ} {w : ℝ × ℝ → ℂ} (hw : MemLp w 2 (B0579.cellMeasure c m))
    {a : ℝ × ℝ → ℝ} (ha : B0579.IsCylTest c a) :
    IntegrableOn (fun x => w x * (a x : ℂ)) (B0579.cell c) := by
  obtain ⟨R0, hR0⟩ := ha.band
  refine RateSplitAux.integrableOn_w_mul c m (R0 / 2) hw
    (Complex.continuous_ofReal.comp ha.continuous) ?_
  intro x hx
  have h1 : R0 < |x.2| := by linarith
  simp [hR0 x h1]

end LadPRWeakAux

open LadPRWeakAux in
/-- The flow integral for a complex test split into real and imaginary parts. -/
lemma flow_integral_split {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {t : ℝ}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hf : IsLinearisedFlow ν c m tr t f w u) {a b : ℝ × ℝ → ℝ}
    (ha : B0579.IsCylTest c a) (hb : B0579.IsCylTest c b)
    {Ψ : ℝ × ℝ → ℂ} (hΨ : ∀ x, Ψ x = (a x : ℂ) + (b x : ℂ) * Complex.I) {σ : ℝ} (hσ : t ≤ σ) :
    ∫ x in B0579.cell c, ladFlowCx tr (w σ) (u σ) σ Ψ x =
      (∫ x in B0579.cell c, flowIntegrand tr (w σ) (u σ) σ a x) +
        (∫ x in B0579.cell c, flowIntegrand tr (w σ) (u σ) σ b x) * Complex.I := by
  have hΨf : Ψ = fun y => (a y : ℂ) + (b y : ℂ) * Complex.I := funext hΨ
  have hpt : ∀ x, ladFlowCx tr (w σ) (u σ) σ Ψ x =
      flowIntegrand tr (w σ) (u σ) σ a x + flowIntegrand tr (w σ) (u σ) σ b x * Complex.I :=
    fun x => by
      rw [show ladFlowCx tr (w σ) (u σ) σ Ψ x =
        ladFlowCx tr (w σ) (u σ) σ (fun y => (a y : ℂ) + (b y : ℂ) * Complex.I) x from
          congrArg (fun F : ℝ × ℝ → ℂ => ladFlowCx tr (w σ) (u σ) σ F x) hΨf]
      exact LadPRWeakAux.ladFlow_split tr (w σ) (u σ) σ ha hb x
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  rw [integral_add (hf.integrable a ha σ hσ) ((hf.integrable b hb σ hσ).mul_const Complex.I),
    integral_mul_const]

open LadPRWeakAux in
/-- The weak identity at a fixed time, for a complex test split into real parts. -/
lemma weak_split {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {t : ℝ}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hf : IsLinearisedFlow ν c m tr t f w u) {a b : ℝ × ℝ → ℝ}
    (ha : B0579.IsCylTest c a) (hb : B0579.IsCylTest c b)
    {Ψ : ℝ × ℝ → ℂ} (hΨ : ∀ x, Ψ x = (a x : ℂ) + (b x : ℂ) * Complex.I) {s : ℝ} (hts : t ≤ s) :
    ∫ x in B0579.cell c, w s x * Ψ x = (∫ x in B0579.cell c, f x * Ψ x) +
      ∫ r in t..s, ((∫ x in B0579.cell c, flowIntegrand tr (w r) (u r) r a x) +
        (∫ x in B0579.cell c, flowIntegrand tr (w r) (u r) r b x) * Complex.I) := by
  have hΨf : Ψ = fun y => (a y : ℂ) + (b y : ℂ) * Complex.I := funext hΨ
  have hwa := integ_w (hf.memX s hts) ha
  have hwb := integ_w (hf.memX s hts) hb
  have hfa : IntegrableOn (fun x => f x * (a x : ℂ)) (B0579.cell c) := by
    refine (integ_w (hf.memX t le_rfl) ha).congr_fun_ae ?_
    filter_upwards [hf.initial] with x hx
    simp only [hx]
  have hfb : IntegrableOn (fun x => f x * (b x : ℂ)) (B0579.cell c) := by
    refine (integ_w (hf.memX t le_rfl) hb).congr_fun_ae ?_
    filter_upwards [hf.initial] with x hx
    simp only [hx]
  have e_w : ∫ x in B0579.cell c, w s x * Ψ x =
      (∫ x in B0579.cell c, w s x * (a x : ℂ)) + (∫ x in B0579.cell c, w s x * (b x : ℂ)) * Complex.I := by
    rw [← integral_mul_const, ← integral_add hwa (hwb.mul_const Complex.I)]
    congr 1
    funext x
    rw [hΨ x]
    ring
  have e_f : ∫ x in B0579.cell c, f x * Ψ x =
      (∫ x in B0579.cell c, f x * (a x : ℂ)) + (∫ x in B0579.cell c, f x * (b x : ℂ)) * Complex.I := by
    rw [← integral_mul_const, ← integral_add hfa (hfb.mul_const Complex.I)]
    congr 1
    funext x
    rw [hΨ x]
    ring
  have Wa := hf.weak a ha s hts
  have Wb := hf.weak b hb s hts
  have hIa : IntervalIntegrable (fun r => ∫ x in B0579.cell c, flowIntegrand tr (w r) (u r) r a x)
      volume t s := hf.timeIntegrable a ha s hts
  have hIb : IntervalIntegrable (fun r => ∫ x in B0579.cell c, flowIntegrand tr (w r) (u r) r b x)
      volume t s := hf.timeIntegrable b hb s hts
  rw [e_w, e_f, Wa, Wb, intervalIntegral.integral_add hIa (hIb.mul_const Complex.I),
    intervalIntegral.integral_mul_const]
  ring

open LadPRWeakAux in
/-- **Leaf 2** (weak identity between two times). -/
theorem ladPRWeak : LadPRWeak := by
  intro ν c m tr t f w u hf Ψ hre him a b hta hab
  have hΨ : ∀ x, Ψ x = (((Ψ x).re : ℝ) : ℂ) + (((Ψ x).im : ℝ) : ℂ) * Complex.I :=
    fun x => (Complex.re_add_im _).symm
  have hS : ∀ s, t ≤ s → ∫ x in B0579.cell c, w s x * Ψ x = (∫ x in B0579.cell c, f x * Ψ x) +
      ∫ r in t..s, ((∫ x in B0579.cell c, flowIntegrand tr (w r) (u r) r (fun x => (Ψ x).re) x) +
        (∫ x in B0579.cell c, flowIntegrand tr (w r) (u r) r (fun x => (Ψ x).im) x) * Complex.I) :=
    fun s hs => weak_split hf hre him hΨ hs
  have hGb : IntervalIntegrable (fun r => (∫ x in B0579.cell c,
      flowIntegrand tr (w r) (u r) r (fun x => (Ψ x).re) x) +
        (∫ x in B0579.cell c, flowIntegrand tr (w r) (u r) r (fun x => (Ψ x).im) x) * Complex.I)
      volume t b :=
    (hf.timeIntegrable _ hre b (hta.trans hab)).add
      ((hf.timeIntegrable _ him b (hta.trans hab)).mul_const Complex.I)
  have hGa : IntervalIntegrable (fun r => (∫ x in B0579.cell c,
      flowIntegrand tr (w r) (u r) r (fun x => (Ψ x).re) x) +
        (∫ x in B0579.cell c, flowIntegrand tr (w r) (u r) r (fun x => (Ψ x).im) x) * Complex.I)
      volume t a :=
    (hf.timeIntegrable _ hre a hta).add
      ((hf.timeIntegrable _ him a hta).mul_const Complex.I)
  have hint : ∫ σ in a..b, (∫ x in B0579.cell c, ladFlowCx tr (w σ) (u σ) σ Ψ x) =
      ∫ σ in a..b, ((∫ x in B0579.cell c,
        flowIntegrand tr (w σ) (u σ) σ (fun x => (Ψ x).re) x) +
        (∫ x in B0579.cell c, flowIntegrand tr (w σ) (u σ) σ (fun x => (Ψ x).im) x) * Complex.I) := by
    refine intervalIntegral.integral_congr (fun σ hσ => ?_)
    rw [Set.uIcc_of_le hab] at hσ
    exact flow_integral_split hf hre him hΨ (le_trans hta hσ.1)
  rw [hint, hS b (hta.trans hab), hS a hta]
  have := intervalIntegral.integral_interval_sub_left hGb hGa
  linear_combination this

end UnforcedLeray.Short.IIIa
