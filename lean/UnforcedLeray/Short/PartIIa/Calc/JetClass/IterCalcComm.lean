import UnforcedLeray.Short.PartIIa.Calc.JetClass
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.IterComm
import UnforcedLeray.Short.PartIIa.Tasks.R02.Commutators

/-!
# Part II-a, jet-class calculus: iterated commutators on single profiles (`IterCalcComm`)

Target: `UnforcedLeray.Short.PartIIa.Jet.iterCalcComm : IterCalcComm` (`Calc/JetClass.lean`).

Source of record: `the November 2 reference manuscript`, lines 1243-1272.

Proof route (all on the open set `{s > 0}`):
* `∂_q ∂_η = ∂_η ∂_q` on smooth functions (`profDir_comm`), so `∂_q^b ∂_η = ∂_η ∂_q^b`;
* `∂_q K = K ∂_q` (`partialQ_ageOperator`), so `∂_q^b K = K ∂_q^b`;
* `∂_η K = K ∂_η + ∂_η` (`commut_partialEta_ageOperator` and mixed-partial symmetry), so
  `∂_η^a K = (K + a) ∂_η^a` by induction on `a`, with linearity of `∂_η` at points of
  differentiability (`partialEta_add_mul`).
Each step is an induction, using that the operators respect equality on `{s > 0}`
(`IterComm.iterLifts_q`, `IterComm.iterLifts_eta`) and that the iterates stay smooth there.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

/-- A smooth function on `{s > 0}` is `C²` at each of its points with `s > 0`. -/
theorem ic_c2 {H : ProfilePoint → ℝ} (hH : ContDiffOn ℝ ∞ H {x : ProfilePoint | 0 < x.2.2})
    {x : ProfilePoint} (hx : 0 < x.2.2) : ContDiffAt ℝ 2 H x :=
  (hH.contDiffAt (UnforcedLeray.Short.PartIIa.isOpen_late.mem_nhds hx)).of_le (by norm_num)

/-- Pointwise `∂_q ∂_η H = ∂_η ∂_q H` for `H` smooth on `{s > 0}`. -/
theorem ic_comm_QE {H : ProfilePoint → ℝ} (hH : ContDiffOn ℝ ∞ H {x : ProfilePoint | 0 < x.2.2})
    {x : ProfilePoint} (hx : 0 < x.2.2) :
    partialQ (partialEta H) x = partialEta (partialQ H) x :=
  UnforcedLeray.Short.PartIIa.IterComm.profDir_comm hH hx eqDir eηDir

/-- Pointwise `∂_q K H = K ∂_q H` for `H` smooth on `{s > 0}`. -/
theorem ic_comm_QK {H : ProfilePoint → ℝ} (hH : ContDiffOn ℝ ∞ H {x : ProfilePoint | 0 < x.2.2})
    {x : ProfilePoint} (hx : 0 < x.2.2) :
    partialQ (ageOperator H) x = ageOperator (partialQ H) x :=
  partialQ_ageOperator (ic_c2 hH hx)

/-- Pointwise `∂_η K H = K ∂_η H + ∂_η H` for `H` smooth on `{s > 0}`. -/
theorem ic_comm_EK {H : ProfilePoint → ℝ} (hH : ContDiffOn ℝ ∞ H {x : ProfilePoint | 0 < x.2.2})
    {x : ProfilePoint} (hx : 0 < x.2.2) :
    partialEta (ageOperator H) x = ageOperator (partialEta H) x + partialEta H x := by
  rw [UnforcedLeray.Short.PartIIa.commut_partialEta_ageOperator (ic_c2 hH hx)]
  unfold ageOperator
  rw [UnforcedLeray.Short.PartIIa.commut_partialEta_partialAge (ic_c2 hH hx)]
  ring

/-- `∂_q^b ∂_η f = ∂_η ∂_q^b f` on `{s > 0}`. -/
theorem ic_qE {f : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f {x : ProfilePoint | 0 < x.2.2})
    (b : ℕ) :
    EqOn (partialQ^[b] (partialEta f)) (partialEta (partialQ^[b] f))
      {x : ProfilePoint | 0 < x.2.2} := by
  induction b with
  | zero => intro x _; rfl
  | succ b ih =>
    intro x hx
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rw [UnforcedLeray.Short.PartIIa.IterComm.iterLifts_q ih hx]
    exact ic_comm_QE (contDiffOn_partialQ_iter hf b) hx

/-- `∂_q^b K f = K ∂_q^b f` on `{s > 0}`. -/
theorem ic_qK {f : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f {x : ProfilePoint | 0 < x.2.2})
    (b : ℕ) :
    EqOn (partialQ^[b] (ageOperator f)) (ageOperator (partialQ^[b] f))
      {x : ProfilePoint | 0 < x.2.2} := by
  induction b with
  | zero => intro x _; rfl
  | succ b ih =>
    intro x hx
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rw [UnforcedLeray.Short.PartIIa.IterComm.iterLifts_q ih hx]
    exact ic_comm_QK (contDiffOn_partialQ_iter hf b) hx

/-- `∂_η^a K f = K ∂_η^a f + a ∂_η^a f` on `{s > 0}`. -/
theorem ic_etaK {f : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f {x : ProfilePoint | 0 < x.2.2})
    (a : ℕ) :
    EqOn (partialEta^[a] (ageOperator f))
      (fun x => ageOperator (partialEta^[a] f) x + (a : ℝ) * (partialEta^[a] f) x)
      {x : ProfilePoint | 0 < x.2.2} := by
  induction a with
  | zero => intro x _; simp
  | succ a ih =>
    intro x hx
    dsimp only
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rw [UnforcedLeray.Short.PartIIa.IterComm.iterLifts_eta ih hx]
    have hG : ContDiffOn ℝ ∞ (partialEta^[a] f) {x : ProfilePoint | 0 < x.2.2} :=
      contDiffOn_partialEta_iter hf a
    have hK : DifferentiableAt ℝ (ageOperator (partialEta^[a] f)) x :=
      differentiableAt_ageOperator (ic_c2 hG hx)
    have hD : DifferentiableAt ℝ (partialEta^[a] f) x :=
      (ic_c2 hG hx).differentiableAt (by norm_num)
    rw [partialEta_add_mul hK hD (a : ℝ)]
    rw [ic_comm_EK hG hx]
    push_cast
    ring

/-- **Commutators of `K` and the profile derivatives on `{s > 0}`** (`IterCalcComm`). -/
theorem iterCalcComm : IterCalcComm := by
  unfold IterCalcComm
  intro f hf a b
  exact ⟨ic_qE hf b, ic_qK hf b, ic_etaK hf a⟩

end UnforcedLeray.Short.PartIIa.Jet
