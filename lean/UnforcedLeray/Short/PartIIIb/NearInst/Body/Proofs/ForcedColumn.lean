import UnforcedLeray.Short.PartIIIb.NearInst.Targets
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Forced
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.FlatColumn
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.ColumnComparison
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.BodyCoeff
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.BodyGeom
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.BodyWindow
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.BodyFormNorm
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.GainInvContract
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.WindowCutoff
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.CellPtInvH

/-!
# The forced column from the inputs (source 4079-4132)

Source of record: `the November 2 reference manuscript`, lines 4079-4132.

`forcedColumnC_of_inputs` assembles `ForcedColumnC` from the near solver `NearSolverC`, the flat
and body leaves, and the Part III-a coefficient and transverse-tail inputs.  The proof is the
one-term application of the column lemmas, with the restated forced-column assembly
`forcedColumnC_of_slow` (the slow age `Σ` and growing eigenpair `(λ, q)` of the inlet are
quantified; source 2048-2049, 2347-2358, 2385-2387).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Body

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0223
open UnforcedLeray.B0220 (HSpace measureH Profile)

/-- The resolvent split of the forced column (source 4126-4132). -/
theorem fcSplit {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (G : Z ≃L[ℝ] Z) (Dinv D0inv : Z →L[ℝ] Z) (u u0 : Z) :
    ‖G.symm (Dinv u - D0inv u0)‖ ≤
      ‖conjG G Dinv‖ * ‖G.symm (u - u0)‖ + ‖conjG G (Dinv - D0inv)‖ * ‖G.symm u0‖ := by
  have e : G.symm (Dinv u - D0inv u0) =
      conjG G Dinv (G.symm (u - u0)) + conjG G (Dinv - D0inv) (G.symm u0) := by
    simp [conjG_apply, map_sub]
  rw [e]
  exact (norm_add_le _ _).trans
    (add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _))

theorem fcMono {a x y e e' n : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hxy : x ≤ y) (he0 : 0 ≤ e)
    (he : e ≤ e') (hn : 0 ≤ n) : a * x * e * n ≤ a * y * e' * n :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_left hxy ha) he he0 (mul_nonneg ha (hx.trans hxy))) hn

/-- **`ForcedColumnC`** (source 4079-4132) from the near solver and the two column statements,
with the slow age `Σ` and the growing eigenpair of the planar reference quantified. -/
theorem forcedColumnC_of_slow (hNS : NearSolverC) (hU0 : FlatBodyColumnBound)
    (hUD : BodyColumnComparison) : ForcedColumnC := by
  intro P hP Kset hK hKsub mZ hmZ dm dp hdm
  obtain ⟨K1, hK1⟩ := hNS P hP Kset hK hKsub mZ hmZ dm dp hdm
  obtain ⟨K2, hK2⟩ := hUD Kset hK hKsub mZ hmZ dm dp hdm
  refine ⟨max K1 K2, ?_⟩
  intro a b δ m0 Dp ha hb hb1 hKab hδ hm0 hm0dm hη hm0θ hDp C0 k0 hC0 c₁ c₂ rmax hc₁ hc12
    hrmax Sig hSig
  have hab : 0 ≤ a + b := by linarith
  have hKab1 : (K1 : ℝ) * (a + b) < 1 / 100 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left K1 K2) hab) hKab
  have hKab2 : (K2 : ℝ) * (a + b) < 1 / 14 := by
    have : (K2 : ℝ) * (a + b) ≤ ((max K1 K2 : ℕ) : ℝ) * (a + b) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right K1 K2) hab
    linarith
  obtain ⟨C1, k1, ν1, hν1, h1⟩ := hK1 a b δ m0 Dp ha hb hb1 hKab1 hδ hm0 hm0dm hη hm0θ hDp C0
    k0 hC0 c₁ c₂ rmax hc₁ hc12 hrmax Sig hSig
  obtain ⟨c2, C2, k2, ν2, hc2, hν2, h2⟩ := hK2 a b m0 ha hb hb1 hKab2 hm0 hm0dm C0 k0 hC0
    Sig P.eigenvalue P.mode hSig hP.eigenpair
  obtain ⟨C3, k3, ν3, hν3, h3⟩ := hU0 Kset hK hKsub mZ hmZ dm dp hdm
  have hγ : 0 < P.eigenvalue.re := hP.eigenpair.re_pos
  have hθ : 0 < thetaAB a b * (P.eigenvalue.re / 3) := by
    refine mul_pos ?_ (by linarith)
    unfold thetaAB
    exact lt_min (lt_min (by linarith) (by linarith)) (lt_min (by norm_num) (by norm_num))
  set θ := thetaAB a b * (P.eigenvalue.re / 3) with hθdef
  refine ⟨min c2 (θ / 2), |C1| * (|C2| + |C3|), k1 + k2 + k3, min (min ν1 ν2) (min ν3 1),
    lt_min hc2 (by linarith), lt_min (lt_min hν1 hν2) (lt_min hν3 one_pos), ?_⟩
  intro p d hBG hpν hage hmode hε S_in V rb hsplit hSin μ hμ o hact Reps R0 hReps hR0 f
  have hν := p.ν_pos
  have hν1' : p.ν ≤ ν1 := hpν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν2' : p.ν ≤ ν2 := hpν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν3' : p.ν ≤ ν3 := hpν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν1'' : p.ν ≤ 1 := hpν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hρ : 0 < UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 := by
    unfold UnforcedLeray.Short.IIb.rhoB
    have h1 := p.ν_pos
    have h2 := p.ε_pos
    positivity
  obtain ⟨-, -, hDN, hDiff, -⟩ := h1 p d hBG hν1' hage hmode hε S_in V rb hsplit hSin μ hμ o hact
  have hU := h2 p d hBG hν2' hage hmode S_in V rb hsplit P.eigenvalue.re hγ.le μ hμ o.M0 o.MU
    hact.flat hact.split Reps R0 hReps hR0 f
  have hU0' := h3 p d hBG hν3' (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) P.eigenvalue.re hρ hγ.le
    μ hμ o.M0 hact.flat R0 hR0 f
  -- the polynomial and exponential factors
  have hX : 1 ≤ p.ν⁻¹ := by rw [le_inv_comm₀ one_pos hν, inv_one]; exact hν1''
  have hXpos : ∀ j : ℕ, 0 < p.ν⁻¹ ^ j := fun j => pow_pos (inv_pos.2 hν) j
  have hE2 : Real.exp (-c2 / p.ν) ≤ Real.exp (-min c2 (θ / 2) / p.ν) := by
    apply Real.exp_le_exp.2
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_right (min_le_left _ _) hν.le
  have hEθ : Real.exp (-θ / (2 * p.ν)) ≤ Real.exp (-min c2 (θ / 2) / p.ν) := by
    apply Real.exp_le_exp.2
    rw [show -θ / (2 * p.ν) = -(θ / 2) / p.ν by ring, neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_right (min_le_right _ _) hν.le
  have hP12 : p.ν⁻¹ ^ k1 * p.ν⁻¹ ^ k2 ≤ p.ν⁻¹ ^ (k1 + k2 + k3) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hX (by omega)
  have hP13 : p.ν⁻¹ ^ k1 * p.ν⁻¹ ^ k3 ≤ p.ν⁻¹ ^ (k1 + k2 + k3) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hX (by omega)
  -- the four factors
  have hA1 : ‖conjG (gainEquiv p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) P.eigenvalue.re
      p.ν_pos) (Ring.inverse o.DN)‖ ≤ |C1| * p.ν⁻¹ ^ k1 :=
    hDN.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (hXpos _).le)
  have hA2 : ‖conjG (gainEquiv p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) P.eigenvalue.re
      p.ν_pos) (Ring.inverse o.DN - Ring.inverse o.D0)‖ ≤
        |C1| * p.ν⁻¹ ^ k1 * Real.exp (-θ / (2 * p.ν)) :=
    hDiff.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) (hXpos _).le) (Real.exp_pos _).le)
  have hB1 : ‖(gainEquiv p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) P.eigenvalue.re
      p.ν_pos).symm (o.MU (Reps f) - o.M0 (R0 f))‖ ≤
        |C2| * p.ν⁻¹ ^ k2 * Real.exp (-c2 / p.ν) * ‖f‖ :=
    hU.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) (hXpos _).le) (Real.exp_pos _).le)
      (norm_nonneg _))
  have hB2 : ‖(gainEquiv p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) P.eigenvalue.re
      p.ν_pos).symm (o.M0 (R0 f))‖ ≤ |C3| * p.ν⁻¹ ^ k3 * ‖f‖ :=
    hU0'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) (hXpos _).le) (norm_nonneg _))
  have hc1 : 0 ≤ |C1| * p.ν⁻¹ ^ k1 := mul_nonneg (abs_nonneg _) (hXpos _).le
  refine (fcSplit _ _ _ _ _).trans ?_
  calc _ ≤ (|C1| * p.ν⁻¹ ^ k1) * (|C2| * p.ν⁻¹ ^ k2 * Real.exp (-c2 / p.ν) * ‖f‖) +
        (|C1| * p.ν⁻¹ ^ k1 * Real.exp (-θ / (2 * p.ν))) * (|C3| * p.ν⁻¹ ^ k3 * ‖f‖) :=
        add_le_add (mul_le_mul hA1 hB1 (norm_nonneg _) hc1)
          (mul_le_mul hA2 hB2 (norm_nonneg _) (mul_nonneg hc1 (Real.exp_pos _).le))
    _ = (|C1| * |C2|) * (p.ν⁻¹ ^ k1 * p.ν⁻¹ ^ k2) * Real.exp (-c2 / p.ν) * ‖f‖ +
        (|C1| * |C3|) * (p.ν⁻¹ ^ k1 * p.ν⁻¹ ^ k3) * Real.exp (-θ / (2 * p.ν)) * ‖f‖ := by ring
    _ ≤ (|C1| * |C2|) * p.ν⁻¹ ^ (k1 + k2 + k3) * Real.exp (-min c2 (θ / 2) / p.ν) * ‖f‖ +
        (|C1| * |C3|) * p.ν⁻¹ ^ (k1 + k2 + k3) * Real.exp (-min c2 (θ / 2) / p.ν) * ‖f‖ :=
        add_le_add
          (fcMono (mul_nonneg (abs_nonneg _) (abs_nonneg _))
            (mul_nonneg (hXpos _).le (hXpos _).le) hP12 (Real.exp_pos _).le hE2 (norm_nonneg _))
          (fcMono (mul_nonneg (abs_nonneg _) (abs_nonneg _))
            (mul_nonneg (hXpos _).le (hXpos _).le) hP13 (Real.exp_pos _).le hEθ (norm_nonneg _))
    _ = |C1| * (|C2| + |C3|) * p.ν⁻¹ ^ (k1 + k2 + k3) * Real.exp (-min c2 (θ / 2) / p.ν) *
        ‖f‖ := by ring

/-- **The forced column from its inputs** (source 4079-4132): the one-term assembly of the near
solver, the flat column bound, the column comparison (coefficient, geometric and window parts),
with the body form norm and the cell recentring identities. -/
theorem forcedColumnC_of_inputs (hNS : NearSolverC) (hFT : FlatTrainMultBound)
    (hM1 : Delta.TrainMultRestr) (hM2 : Delta.ThinDiffMult) (hM3 : Delta.BroadMult)
    (hSC : Delta.RawStreamCompletion) (hRep : Delta.RepairCoeffBound)
    (hRE : UnforcedLeray.Short.IIIa.RawCoeffEarly) (hRL : UnforcedLeray.Short.IIIa.RawCoeffLate)
    (hIn : UnforcedLeray.Short.IIIa.InletCoeffBounds)
    (hRT : UnforcedLeray.Short.IIIa.RawTransverseTail)
    (hCF : UnforcedLeray.Short.PartIIa.NearCompactFreeComparison) : ForcedColumnC := by
  have hH : ∀ c : ℝ, 0 < c → Masked.CellPtH c := fun c hc => Masked.cellPtH_aux c hc
  have hHi : ∀ c : ℝ, 0 < c → Masked.CellPtInvH c := fun c hc => Masked.cellPtInvH_eq c hc
  have hN : BodyFormNorm := bodyFormNorm_of hH hHi
  exact forcedColumnC_of_slow hNS (flatBodyColumnBound_of hM1 hFT gainInvContract hN)
    (bodyColumnComparison_of (bodyCoeffColumn_of hM2 hM3 hSC hRep hIn gainInvContract)
      (bodyGeomColumn_of hM1 hFT hSC hRE hRL hRT gainInvContract hN
        (bodyWindowComparison_of hCF windowCutoffExists hH hHi)) hN)

end UnforcedLeray.Short.PartIIIb.NearInst.Body
