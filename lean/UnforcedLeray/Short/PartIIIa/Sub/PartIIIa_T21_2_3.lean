import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.Adjoint

/-!
# Part III-a, `PartIII-a:T21/2/3`: the duality pairing bound, decomposed

Source of record: `the November 2 reference manuscript` (SP), lines 3036-3040
(`<J_a⁻¹ f, φ> = a<f, φ(·/√a)>`), 3044 (equivalence of `p_d` and `⟨y⟩^{2m}`), 3074-3075 (duality).

`AdjointPairingBound m` is the chain
`∫_{C_{d_s}} W(z_s)G = ∫_{C_c} w(s) g = ∫_{C_c} f φ(t) = ∫_{C_{d_t}} J_{a_t}⁻¹f Φ(z_t)`, then
`|∫ F Φ| ≤ ‖F‖_{(H¹_{-m})*} ‖Φ‖_{H¹_{-m}}`, `‖Φ‖_{H¹_{-m}} ≤ C (E_0 + E_1)^{1/2}`.
Leaves:
* `LinAdjDuality`: the weak duality between the linearised weak flow and the weak adjoint
  (SP 3074-3075; the hard core, `IsLinearisedFlow.weak` tested against `IsAdjointFlow.weak`).
* `PairingCoV`: the change of variables `x = √a y` (SP 3036-3037).
* `MovingPhiH1`: `Φ(z_t)` is a weak `H¹_{-m,d_t}` function with classical derivatives (smooth and
  `d_t`-periodic, so the cell integration by parts has no boundary term).
* `H1BySeminorm`: `‖Φ‖²_{H¹_{-m,d}} ≤ C(E_0 + E_1)` (SP 3044: `⟨y⟩^{-2m} ≤ p_d⁻¹`, `|sin u| ≤ |u|`).
* `NegNormPairing`: `|∫FΦ| ≤ ‖F‖_{Z⁻¹} ‖Φ‖_{H¹}` for finite `‖Φ‖_{H¹}` (definition of `negNorm`).
`adjointPairingBound_of` assembles them; `revAge_deltaZ` is proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Weak duality** (SP 3074-3075): `∫_{C_c} w(s) g = ∫_{C_c} f φ(t)` for the weak linearised flow
`w` from `f` at age `t` and the weak reverse-time adjoint `φ` with terminal datum `g` at age `s`. -/
def LinAdjDuality (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ g : ℝ × ℝ → ℂ, ∀ φ : ℝ → ℝ × ℝ → ℂ,
      IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s g φ →
      ∀ f : ℝ × ℝ → ℂ, MemLp f 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) →
        HasZeroCirculation (ν ^ (-2 : ℝ)) f →
        ∀ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u →
          ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w s x * g x =
            ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f x * φ t x

/-- **Change of variables** `x = √a y` (SP 3036-3037): `∫_{C_{c/√a}} (J_a⁻¹F) G = ∫_{C_c} F (physAdj a G)`. -/
def PairingCoV : Prop :=
  ∀ c a : ℝ, 0 < c → 0 < a → ∀ F G : ℝ × ℝ → ℂ,
    ∫ y in B0579.cell (cellLen c a), JscaleInv a F y * G y =
      ∫ x in B0579.cell c, F x * physAdj a G x

/-- **The moving adjoint at the initial age is an `H¹_{-m,d_t}` function** (SP 3044, 3074-3075):
`Φ = movingPhi ν φ t` is smooth and `d_t`-periodic (from `IsAdjointFlow.smooth/periodic`), so
its classical derivatives are its weak derivatives on the cell, and `Φ`, `∇Φ` lie in
`X_{-m,d_t}` (scaling of the weighted norm by `a_t`, `memX`, `memH1` at `r = t`). -/
def MovingPhiH1 (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ g : ℝ × ℝ → ℂ, ∀ φ : ℝ → ℝ × ℝ → ℂ,
      IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s g φ →
      (∀ j, HasWeakCellDerivC (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) j (movingPhi ν φ t)
        (pdCx j (movingPhi ν φ t))) ∧
      MemLp (movingPhi ν φ t) 2
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) (-m)) ∧
      ∀ j, MemLp (pdCx j (movingPhi ν φ t)) 2
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) (-m))

/-- **`H¹_{-m}` norm by the periodic-weight energies** (SP 3044): for `m ≥ 0` there is `C`, uniform
in `d > 0`, with `‖Φ‖_{H¹_{-m,d}} ≤ C (E_0 + E_1)^{1/2}` for `Φ, ∇Φ ∈ X_{-m,d}`
(`⟨y⟩^{-2m} ≤ p_d⁻¹` from `|sin u| ≤ |u|`; `p_d⁻¹ ≤ C⟨y⟩^{-2m}` on the centered cell shows the
integrals are finite). -/
def H1BySeminorm (m : ℝ) : Prop :=
  0 ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 0 < d → ∀ Φ : ℝ × ℝ → ℂ,
    MemLp Φ 2 (B0579.cellMeasure d (-m)) →
    (∀ j, MemLp (pdCx j Φ) 2 (B0579.cellMeasure d (-m))) →
    h1Norm d m Φ (fun j => pdCx j Φ) ≤
      ENNReal.ofReal (C * Real.sqrt (adjE0 d m Φ + adjE1 d m Φ))

/-- **The `negNorm` pairing bound** (definition of `negNorm`, SP 2823-2826): for `Φ` with weak
derivatives `g` and finite `h1Norm`, `|∫FΦ| ≤ ‖F‖_{Z⁻¹} ‖Φ‖_{H¹_{-m}}`. -/
def NegNormPairing : Prop :=
  ∀ c m : ℝ, ∀ F Φ : ℝ × ℝ → ℂ, ∀ g : Fin 2 → ℝ × ℝ → ℂ,
    (∀ j, HasWeakCellDerivC c j Φ (g j)) → h1Norm c m Φ g ≠ ⊤ →
    ENNReal.ofReal ‖∫ x in B0579.cell c, F x * Φ x‖ ≤ negNorm c m F * h1Norm c m Φ g

theorem revAge_deltaZ {ν t s : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) :
    revAge ν s (deltaZ ν t s) = t := by
  have ha : clockA ν t ≠ 0 := by unfold clockA; positivity
  unfold revAge deltaZ ageOfZ movingZ clockA at *
  have : s / (1 + ν * s) - (s / (1 + ν * s) - t / (1 + ν * t)) = t / (1 + ν * t) := by ring
  rw [this]
  have h1 : (1 + ν * t) ≠ 0 := by positivity
  field_simp
  ring

theorem physAdj_movingPhi {ν : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 ≤ t) (φ : ℝ → ℝ × ℝ → ℂ)
    (x : ℝ × ℝ) : physAdj (clockA ν t) (movingPhi ν φ t) x = φ t x := by
  have ha : 0 < clockA ν t := by unfold clockA; positivity
  have hs : Real.sqrt (clockA ν t) ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  unfold physAdj movingPhi
  have e1 : Real.sqrt (clockA ν t) * (x.1 / Real.sqrt (clockA ν t)) = x.1 := by field_simp
  have e2 : Real.sqrt (clockA ν t) * (x.2 / Real.sqrt (clockA ν t)) = x.2 := by field_simp
  rw [e1, e2]
  have : ((clockA ν t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  push_cast
  field_simp

/-- **Assembly** of `AdjointPairingBound` (SP 3036-3040, 3044, 3074-3075) from the every-train
duality `LinAdjDuality` (`ν₀ = 1`). The route used is the BUC assembly
`adjointPairingBoundBUC_of` (`Sub/T21_2_3/PairingBoundBUC.lean`, from `LinAdjDualityBUC`). -/
theorem adjointPairingBound_of (m : ℝ) (hm : 0 ≤ m) (h1 : LinAdjDuality m) (h2 : PairingCoV)
    (h3 : MovingPhiH1 m) (h4 : H1BySeminorm m) (h5 : NegNormPairing) :
    AdjointPairingBound m := by
  obtain ⟨C, hC0, hC⟩ := h4 hm
  refine ⟨C, 1, hC0, one_pos, ?_⟩
  intro ν hν' tr _ t s ht hts G hG φ hφ f hf hf0 w u hw
  have hν : 0 < ν := hν'.1
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have has : 0 < clockA ν s := by unfold clockA; have : 0 ≤ s := ht.trans hts.le; positivity
  have hat : 0 < clockA ν t := by unfold clockA; positivity
  have hdt : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν t) := by
    unfold cellLen; exact div_pos hc (Real.sqrt_pos.mpr hat)
  have e1 := h2 _ _ hc has (w s) G
  have e2 := h1 ν hν tr t s ht hts _ φ hφ f hf hf0 w u hw
  have e3 : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f x * φ t x =
      ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)),
        JscaleInv (clockA ν t) f y * movingPhi ν φ t y := by
    rw [h2 _ _ hc hat f (movingPhi ν φ t)]
    simp only [physAdj_movingPhi hν ht]
  obtain ⟨hd, hmem, hmem'⟩ := h3 ν hν tr t s ht hts _ φ hφ
  have hbound := hC _ hdt (movingPhi ν φ t) hmem hmem'
  have hfin : h1Norm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (movingPhi ν φ t)
      (fun j => pdCx j (movingPhi ν φ t)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hp := h5 _ m (JscaleInv (clockA ν t) f) (movingPhi ν φ t) _ hd hfin
  have hrev : revE0 ν (ν ^ (-2 : ℝ)) m φ s (deltaZ ν t s) +
      revE1 ν (ν ^ (-2 : ℝ)) m φ s (deltaZ ν t s) =
      adjE0 (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (movingPhi ν φ t) +
        adjE1 (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m (movingPhi ν φ t) := by
    unfold revE0 revE1
    rw [revAge_deltaZ hν ht]
  rw [e1, e2, e3, hrev]
  exact hp.trans (by gcongr)

end UnforcedLeray.Short.IIIa
