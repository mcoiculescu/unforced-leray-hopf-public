import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Lemmas
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.NearSolver

/-!
# Assembly of `near:deltaN` (source 3927-3942, proof 3956-4053)

Proves `nearDeltaBoundC_of : … → NearDeltaBoundC` (`NearInst/Targets.lean`) from the lemma `Prop`s
of `NearInst/Delta/Lemmas.lean` and the reused statements `IIIa.RawCoeffEarly`,
`IIIa.RawCoeffLate`, `IIIa.InletCoeffBounds`, `IIIa.RawTransverseTail` (`PartIII-a/StressInputs`),
`FlatTrainMultBound`, `NearMaskedFreeBoundC` (`NearInst/Targets.lean`).

Route.  For `F ∈ Z` (`conj_deltaN_apply`, source 4036-4040)
`G⁻¹(D_N - D₀)GF = G⁻¹(M_U - M₀)S_N gF + G⁻¹M₀(S_N - S₀)gF`; the first is split by `fstZ + sndZ = 1`
into the thin difference (`ThinDiffMult`, coefficient `RawStreamCompletion` + `InletCoeffBounds`
with `|α_i| ≤ ρ_b`, third term) and the broad repair (`BroadMult`, `RepairCoeffBound`, fifth term),
both times `‖g⁻¹S_Ng‖ ≤ P_ν e^{η_δ/ν}` (`NearMaskedFreeBoundC`).  The second is split by the output
partition (`OutPartitionSum`): young end (train multiplier `P_ν(ε^{a/2} + ε)`, response `P_ν`; first
term), old end (`P_ν(ε^{b/2} + ε)`, `P_ν`; second term), transverse tail (train `e^{-D_⊥/ν}`,
response `P_ν e^{η_δ/ν}`; last term) and the `N ≤ P_ν` bins (complete block and partial strip;
fourth term, `ε^{1-b/2} ≤ ε^{1/50-K(a+b)}`).  The exponents are collected in `combine`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-! ## Pointwise identities (source 4036-4040) -/

theorem norm_apply_apply_le {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : F →L[ℝ] G) (B : E →L[ℝ] F) (x : E) : ‖A (B x)‖ ≤ ‖A‖ * ‖B‖ * ‖x‖ := by
  calc ‖A (B x)‖ ≤ ‖A‖ * ‖B x‖ := A.le_opNorm _
    _ ≤ ‖A‖ * (‖B‖ * ‖x‖) := mul_le_mul_of_nonneg_left (B.le_opNorm x) (norm_nonneg _)
    _ = ‖A‖ * ‖B‖ * ‖x‖ := by ring

section Pieces

variable {c mZ ρb : ℝ}

/-- `G⁻¹(D_N - D₀)G F = G⁻¹(M_U - M₀)S_N gF + G⁻¹M₀(S_N - S₀)gF` (source 4036-4040). -/
theorem conj_deltaN_apply (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (o : NearOps c mZ ρb)
    (F : Zsp c mZ ρb) :
    conjG (gainEquiv c mZ ρb γ hν) (o.DN - o.D0) F =
      (gainEquiv c mZ ρb γ hν).symm ((o.MU - o.M0) (o.SN (gainEquiv c mZ ρb γ hν F))) +
        (gainEquiv c mZ ρb γ hν).symm (o.M0 ((o.SN - o.S0) (gainEquiv c mZ ρb γ hν F))) := by
  unfold conjG
  rw [NearOps.DN_sub_D0]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearEquiv.coe_coe, map_sub, map_add]
  abel

/-- The thin and broad output components (`fstZ + sndZ = 1`). -/
theorem coeff_piece (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (M : Hsp c →L[ℝ] Zsp c mZ ρb)
    (X : Zsp c mZ ρb →L[ℝ] Hsp c) (F : Zsp c mZ ρb) :
    (gainEquiv c mZ ρb γ hν).symm (M (X (gainEquiv c mZ ρb γ hν F))) =
      gainConjM γ hν (fstZ c mZ ρb ∘L M) (gainConjS γ hν X F) +
        gainConjM γ hν (sndZ c mZ ρb ∘L M) (gainConjS γ hν X F) := by
  rw [gainConjM_apply, gainConjM_apply, gainConjS_apply, ContinuousLinearEquiv.apply_symm_apply,
    ← map_add (gainEquiv c mZ ρb γ hν).symm, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, fstZ_add_sndZ]

/-- An end region: `G⁻¹M1_A X gF = (G⁻¹M1_Ag)(g⁻¹1_A X G)F` (`1_A` is idempotent). -/
theorem end_piece (γ : ℝ) {ν : ℝ} (hν : 0 < ν) {A : Set Chart} (hA : MeasurableSet A)
    (M : Hsp c →L[ℝ] Zsp c mZ ρb) (X : Zsp c mZ ρb →L[ℝ] Hsp c) (F : Zsp c mZ ρb) :
    (gainEquiv c mZ ρb γ hν).symm (M (outRestr c A (X (gainEquiv c mZ ρb γ hν F)))) =
      gainRestrM γ hν A M (gainRestrS γ hν A X F) := by
  simp only [gainRestrM, gainRestrS, gainConjM_apply, gainConjS_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply, outRestr_idem c hA]

/-- The transverse tail: `G⁻¹M1_A X gF = (G⁻¹M1_Ag)(g⁻¹XG)F`. -/
theorem tail_piece (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (A : Set Chart)
    (M : Hsp c →L[ℝ] Zsp c mZ ρb) (X : Zsp c mZ ρb →L[ℝ] Hsp c) (F : Zsp c mZ ρb) :
    (gainEquiv c mZ ρb γ hν).symm (M (outRestr c A (X (gainEquiv c mZ ρb γ hν F)))) =
      gainRestrM γ hν A M (gainConjS γ hν X F) := by
  simp only [gainRestrM, gainConjM_apply, gainConjS_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply]

/-- A bin: the complete block `t < T` plus the rest `t ≥ T` (source 3976-3978). -/
theorem bin_piece (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (A : Set Chart) (T : ℝ)
    (M : Hsp c →L[ℝ] Zsp c mZ ρb) (X : Zsp c mZ ρb →L[ℝ] Hsp c) (F : Zsp c mZ ρb) :
    (gainEquiv c mZ ρb γ hν).symm (M (outRestr c A (X (gainEquiv c mZ ρb γ hν F)))) =
      gainConjM γ hν M (gainBlockS γ hν A (ageBelow T) X F + gainBlockS γ hν A (ageAbove T) X F) := by
  rw [gainConjM_apply, gainBlockS, gainBlockS, gainConjS_apply, gainConjS_apply,
    ← map_add (gainH c γ hν).symm, ContinuousLinearEquiv.apply_symm_apply]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← map_add (outRestr c A), ← map_add X, inRestr_below_add_above]

end Pieces

theorem norm_sum6_le {E : Type*} [NormedAddCommGroup E] (a b u v w : E) (s : Finset ℕ)
    (f : ℕ → E) (A B U V W : ℝ) (g : ℕ → ℝ) (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hu : ‖u‖ ≤ U)
    (hv : ‖v‖ ≤ V) (hw : ‖w‖ ≤ W) (hf : ∀ j ∈ s, ‖f j‖ ≤ g j) :
    ‖a + b + (u + v + w + ∑ j ∈ s, f j)‖ ≤ A + B + (U + V + W + ∑ j ∈ s, g j) := by
  have h1 := norm_add_le (a + b) (u + v + w + ∑ j ∈ s, f j)
  have h2 := norm_add_le a b
  have h3 := norm_add_le (u + v + w) (∑ j ∈ s, f j)
  have h4 := norm_add_le (u + v) w
  have h5 := norm_add_le u v
  have h6 := norm_sum_le s f
  have h7 : ∑ j ∈ s, ‖f j‖ ≤ ∑ j ∈ s, g j := Finset.sum_le_sum hf
  linarith

section Bound

variable {c mZ ρb : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The pointwise decomposition of `δ_N`** (source 3958-4053): `‖G⁻¹(D_N - D₀)G F‖` is bounded by
the thin and broad couplings times `‖g⁻¹S_Ng‖`, the young and old end regions, the transverse tail
and the sum over the bins of the complete blocks and partial strips. -/
theorem deltaN_apply_le (hPart : OutPartitionSum) (γ : ℝ) {ν : ℝ} (hν : 0 < ν)
    (o : NearOps c mZ ρb) {sm S δ : ℝ} (L : ℝ) (hsm : 0 < sm) (hS : sm < S) (hδ : 0 < δ)
    (F : Zsp c mZ ρb) :
    ‖conjG (gainEquiv c mZ ρb γ hν) (o.DN - o.D0) F‖ ≤
      ((‖gainConjM γ hν (fstZ c mZ ρb ∘L (o.MU - o.M0))‖ +
            ‖gainConjM γ hν (sndZ c mZ ρb ∘L (o.MU - o.M0))‖) * ‖gainConjS γ hν o.SN‖ +
        ‖gainRestrM γ hν (ageBelow sm) o.M0‖ * ‖gainRestrS γ hν (ageBelow sm) (o.SN - o.S0)‖ +
        ‖gainRestrM γ hν (ageAbove S) o.M0‖ * ‖gainRestrS γ hν (ageAbove S) (o.SN - o.S0)‖ +
        ‖gainRestrM γ hν (tailSet sm S L) o.M0‖ *
          (‖gainConjS γ hν o.SN‖ + ‖gainConjS γ hν o.S0‖) +
        ∑ j ∈ Finset.range (binCount sm S δ), ‖gainConjM γ hν o.M0‖ *
          (‖gainBlockS γ hν (binSet (binEdge sm S (binCount sm S δ) j)
              (binEdge sm S (binCount sm S δ) (j + 1)) L)
              (ageBelow (Real.exp δ * binEdge sm S (binCount sm S δ) j)) (o.SN - o.S0)‖ +
            ‖gainBlockS γ hν (binSet (binEdge sm S (binCount sm S δ) j)
              (binEdge sm S (binCount sm S δ) (j + 1)) L)
              (ageAbove (Real.exp δ * binEdge sm S (binCount sm S δ) j)) (o.SN - o.S0)‖)) *
        ‖F‖ := by
  rw [conj_deltaN_apply γ hν o F, coeff_piece γ hν (o.MU - o.M0) o.SN F,
    ← hPart c sm S δ L hsm hS hδ ((o.SN - o.S0) (gainEquiv c mZ ρb γ hν F))]
  simp only [map_add, map_sum]
  rw [end_piece γ hν (measurableSet_ageBelow sm), end_piece γ hν (measurableSet_ageAbove S),
    tail_piece γ hν (tailSet sm S L)]
  have hT : ‖gainRestrM γ hν (tailSet sm S L) o.M0 (gainConjS γ hν (o.SN - o.S0) F)‖ ≤
      ‖gainRestrM γ hν (tailSet sm S L) o.M0‖ *
        (‖gainConjS γ hν o.SN‖ + ‖gainConjS γ hν o.S0‖) * ‖F‖ := by
    refine (norm_apply_apply_le _ _ F).trans ?_
    rw [gainConjS_sub]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_sub_le _ _)
      (norm_nonneg _)) (norm_nonneg _)
  calc _ ≤ ‖gainConjM γ hν (fstZ c mZ ρb ∘L (o.MU - o.M0))‖ * ‖gainConjS γ hν o.SN‖ * ‖F‖ +
        ‖gainConjM γ hν (sndZ c mZ ρb ∘L (o.MU - o.M0))‖ * ‖gainConjS γ hν o.SN‖ * ‖F‖ +
        (‖gainRestrM γ hν (ageBelow sm) o.M0‖ *
            ‖gainRestrS γ hν (ageBelow sm) (o.SN - o.S0)‖ * ‖F‖ +
          ‖gainRestrM γ hν (ageAbove S) o.M0‖ *
            ‖gainRestrS γ hν (ageAbove S) (o.SN - o.S0)‖ * ‖F‖ +
          ‖gainRestrM γ hν (tailSet sm S L) o.M0‖ *
            (‖gainConjS γ hν o.SN‖ + ‖gainConjS γ hν o.S0‖) * ‖F‖ +
          ∑ j ∈ Finset.range (binCount sm S δ), ‖gainConjM γ hν o.M0‖ *
            (‖gainBlockS γ hν (binSet (binEdge sm S (binCount sm S δ) j)
                (binEdge sm S (binCount sm S δ) (j + 1)) L)
                (ageBelow (Real.exp δ * binEdge sm S (binCount sm S δ) j)) (o.SN - o.S0)‖ +
              ‖gainBlockS γ hν (binSet (binEdge sm S (binCount sm S δ) j)
                (binEdge sm S (binCount sm S δ) (j + 1)) L)
                (ageAbove (Real.exp δ * binEdge sm S (binCount sm S δ) j)) (o.SN - o.S0)‖) *
              ‖F‖) := by
        refine norm_sum6_le _ _ _ _ _ _ _ _ _ _ _ _ _ (norm_apply_apply_le _ _ F)
          (norm_apply_apply_le _ _ F) (norm_apply_apply_le _ _ F) (norm_apply_apply_le _ _ F)
          hT (fun j _ => ?_)
        rw [bin_piece γ hν _ (Real.exp δ * binEdge sm S (binCount sm S δ) j)]
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (norm_nonneg _)
        rw [add_mul]
        exact add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
    _ = _ := by simp only [add_mul, Finset.sum_mul]; ring

end Bound

/-! ## Numerical bookkeeping -/

theorem exists_pos_le_list : ∀ l : List ℝ, (∀ x ∈ l, 0 < x) → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ x ∈ l, ν₀ ≤ x
  | [], _ => ⟨1, one_pos, by simp⟩
  | x :: l, h => by
    obtain ⟨m, hm, hle⟩ := exists_pos_le_list l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    refine ⟨min x m, lt_min (h x (by simp)) hm, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hle y hy)

theorem up {x C t X Q c : ℝ} {k kk : ℕ} (h : x ≤ C * X ^ k * t) (hX : 1 ≤ X) (hk : k ≤ kk)
    (ht : 0 ≤ t) (hc : max C 0 ≤ c) (hQ : Q = X ^ kk) : x ≤ c * Q * t := by
  have h1 : C * X ^ k ≤ c * X ^ kk :=
    mul_le_mul ((le_max_left C 0).trans hc) (pow_le_pow_right₀ hX hk)
      (pow_nonneg (by linarith) _) ((le_max_right C 0).trans hc)
  rw [hQ]
  exact h.trans (mul_le_mul_of_nonneg_right h1 ht)

theorem up1 {x C X Q c : ℝ} {k kk : ℕ} (h : x ≤ C * X ^ k) (hX : 1 ≤ X) (hk : k ≤ kk)
    (hc : max C 0 ≤ c) (hQ : Q = X ^ kk) : x ≤ c * Q := by
  rw [hQ]
  exact h.trans (mul_le_mul ((le_max_left C 0).trans hc) (pow_le_pow_right₀ hX hk)
    (pow_nonneg (by linarith) _) ((le_max_right C 0).trans hc))

theorem transWeight_nonneg (mZ : ℝ) (p : Chart) :
    0 ≤ UnforcedLeray.Short.IIIa.transWeight mZ p := by
  unfold UnforcedLeray.Short.IIIa.transWeight
  positivity

theorem regime_facts {p : Params} {d dm dp : ℝ} (h : UnforcedLeray.Short.IIb.BgRegime p d dm dp) :
    p.ε < 1 ∧ Real.log p.ε = -d / p.ν := by
  have hd : 0 < d := lt_of_lt_of_le h.dm_pos h.dm_le
  have hν := p.ν_pos
  refine ⟨?_, ?_⟩
  · rw [h.eps_eq, Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (by linarith) hν
  · rw [h.eps_eq, Real.log_exp]

/-- `ρ_b e^{η/ν}` and `√ρ_b e^{η/ν}` are at most `(C₀+1)ν^{-k₀} ε^{3/22}e^{(η+m₀/2)/ν}`
(`ρ_b = C₀ν^{-k₀}e^{m₀/ν}ε^{3/11}`, `m₀ ≤ 3d/11`; source 4047-4049). -/
theorem rhoB_E_le {p : Params} {d dm dp : ℝ} (h : UnforcedLeray.Short.IIb.BgRegime p d dm dp)
    {m0 C0 η : ℝ} (k0 : ℕ) (hm0 : m0 ≤ 3 * d / 11) (hC0 : 0 < C0) (hX : 1 ≤ p.ν⁻¹) :
    UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 * Real.exp (η / p.ν) ≤
        (C0 + 1) * p.ν⁻¹ ^ k0 * (p.ε ^ (3 / 22 : ℝ) * Real.exp ((η + m0 / 2) / p.ν)) ∧
      Real.sqrt (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) * Real.exp (η / p.ν) ≤
        (C0 + 1) * p.ν⁻¹ ^ k0 * (p.ε ^ (3 / 22 : ℝ) * Real.exp ((η + m0 / 2) / p.ν)) := by
  have hν := p.ν_pos
  have hε := p.ε_pos
  obtain ⟨_, hlog⟩ := regime_facts h
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = p.ε ^ (3 / 22 : ℝ) * Real.exp (m0 / (2 * p.ν)) := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; exact mul_pos (Real.rpow_pos_of_pos hε _) (Real.exp_pos _)
  have hu1 : u ≤ 1 := by
    rw [hu, Real.rpow_def_of_pos hε, hlog, ← Real.exp_add, Real.exp_le_one_iff]
    have e1 : -d / p.ν * (3 / 22) + m0 / (2 * p.ν) = (m0 / 2 - 3 * d / 22) * p.ν⁻¹ := by ring
    rw [e1]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (inv_nonneg.2 hν.le)
  have hY : 1 ≤ p.ν⁻¹ ^ k0 := one_le_pow₀ hX
  have hX0 : 0 ≤ p.ν⁻¹ ^ k0 := by linarith
  have hCX : 0 ≤ C0 * p.ν⁻¹ ^ k0 := mul_nonneg hC0.le hX0
  have hu2 : u ^ 2 = Real.exp (m0 / p.ν) * p.ε ^ (3 / 11 : ℝ) := by
    have e1 : (p.ε ^ (3 / 22 : ℝ)) ^ 2 = p.ε ^ (3 / 11 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
      norm_num
    have e2 : Real.exp (m0 / (2 * p.ν)) ^ 2 = Real.exp (m0 / p.ν) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [hu, mul_pow, e1, e2]
    ring
  have hρ : UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 = C0 * p.ν⁻¹ ^ k0 * u ^ 2 := by
    unfold UnforcedLeray.Short.IIb.rhoB
    rw [hu2, ← inv_pow]
    ring
  have hT5 : p.ε ^ (3 / 22 : ℝ) * Real.exp ((η + m0 / 2) / p.ν) = u * Real.exp (η / p.ν) := by
    rw [hu, show (η + m0 / 2) / p.ν = m0 / (2 * p.ν) + η / p.ν by ring, Real.exp_add]
    ring
  have hE0 : 0 < Real.exp (η / p.ν) := Real.exp_pos _
  have huE : 0 ≤ u * Real.exp (η / p.ν) := (mul_pos hu0 hE0).le
  have hw1 : 1 ≤ (C0 + 1) * p.ν⁻¹ ^ k0 := by nlinarith
  have hCw : C0 * p.ν⁻¹ ^ k0 ≤ (C0 + 1) * p.ν⁻¹ ^ k0 := by nlinarith
  rw [hT5, hρ]
  refine ⟨?_, ?_⟩
  · have h1 : C0 * p.ν⁻¹ ^ k0 * u ^ 2 * Real.exp (η / p.ν) =
        (C0 * p.ν⁻¹ ^ k0 * u) * (u * Real.exp (η / p.ν)) := by ring
    rw [h1]
    refine mul_le_mul_of_nonneg_right ?_ huE
    calc C0 * p.ν⁻¹ ^ k0 * u ≤ C0 * p.ν⁻¹ ^ k0 * 1 := mul_le_mul_of_nonneg_left hu1 hCX
      _ ≤ (C0 + 1) * p.ν⁻¹ ^ k0 := by rw [mul_one]; exact hCw
  · have hsq : Real.sqrt (C0 * p.ν⁻¹ ^ k0 * u ^ 2) = Real.sqrt (C0 * p.ν⁻¹ ^ k0) * u := by
      rw [Real.sqrt_mul hCX, Real.sqrt_sq hu0.le]
    rw [hsq]
    have hs : Real.sqrt (C0 * p.ν⁻¹ ^ k0) ≤ (C0 + 1) * p.ν⁻¹ ^ k0 := by
      rw [Real.sqrt_le_left (by linarith)]
      have hww : (C0 + 1) * p.ν⁻¹ ^ k0 ≤ ((C0 + 1) * p.ν⁻¹ ^ k0) ^ 2 := by nlinarith
      linarith
    calc Real.sqrt (C0 * p.ν⁻¹ ^ k0) * u * Real.exp (η / p.ν)
        = Real.sqrt (C0 * p.ν⁻¹ ^ k0) * (u * Real.exp (η / p.ν)) := by ring
      _ ≤ (C0 + 1) * p.ν⁻¹ ^ k0 * (u * Real.exp (η / p.ν)) :=
          mul_le_mul_of_nonneg_right hs huE

/-- The constant of `combine`. -/
def ctot (c : ℝ) : ℝ := 8 * c ^ 3 + 14 * c ^ 2 + 4 * c

set_option maxHeartbeats 1000000 in
/-- **The exponent bookkeeping** (source 3931-3942): the pieces of `deltaN_apply_le`, bounded by the
lemmas, sum to at most `ctot c · Q²ν^{-k₀}ν⁻¹ · deltaNRhs`. -/
theorem combine {Q Y X E D ε ρ sρ eD T1 T2 T3 T4 T5 T6 c : ℝ}
    {n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 : ℝ} {n11 n12 : ℕ → ℝ} {N : ℕ}
    (hQ : 1 ≤ Q) (hY : 1 ≤ Y) (hX : 1 ≤ X) (hE : 1 ≤ E) (hc : 0 ≤ c)
    (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hsρ : 0 ≤ sρ) (heD : 0 ≤ eD)
    (hT1 : 0 ≤ T1) (hT2 : 0 ≤ T2) (hT3 : 0 ≤ T3) (hT4 : 0 ≤ T4) (hT5 : 0 ≤ T5) (hT6 : 0 ≤ T6)
    (hD : D = T1 + T2 + T3 + T4 + T5 + T6)
    (hn3' : 0 ≤ n3) (hn5' : 0 ≤ n5) (hn7' : 0 ≤ n7) (hn9' : 0 ≤ n9) (hn10' : 0 ≤ n10)
    (hn8' : 0 ≤ n8) (hn11' : ∀ j, 0 ≤ n11 j) (hn12' : ∀ j, 0 ≤ n12 j)
    (hn1 : n1 ≤ 2 * (c * Q * ε + 2 * ρ * (c * Q))) (hn2 : n2 ≤ 2 * sρ) (hn3 : n3 ≤ c * Q * E)
    (hn4 : n4 ≤ 2 * (c * Q * T1 + c * Q * ε)) (hn5 : n5 ≤ c * Q)
    (hn6 : n6 ≤ 2 * (c * Q * (T2 + ε) + c * Q * ε)) (hn7 : n7 ≤ c * Q)
    (hn8 : n8 ≤ 2 * eD) (hn9 : n9 ≤ c * Q) (hn10 : n10 ≤ 2 * (c * Q))
    (hn11 : ∀ j ∈ Finset.range N, n11 j ≤ c * Q * T4)
    (hn12 : ∀ j ∈ Finset.range N, n12 j ≤ c * Q * T4)
    (hN : (N : ℝ) ≤ c * X)
    (hεE : ε * E ≤ T3) (hε3 : ε ≤ T3) (hρE : ρ * E ≤ c * Y * T5) (hsρE : sρ * E ≤ c * Y * T5)
    (heDE : eD * E ≤ T6) (heD6 : eD ≤ T6) :
    (n1 + n2) * n3 + n4 * n5 + n6 * n7 + n8 * (n3 + n9) +
        ∑ j ∈ Finset.range N, n10 * (n11 j + n12 j) ≤
      ctot c * (Q ^ 2 * Y * X) * D := by
  have hQ0 : 0 ≤ Q := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hD1 : T1 ≤ D := by rw [hD]; linarith
  have hD2 : T2 ≤ D := by rw [hD]; linarith
  have hD3 : T3 ≤ D := by rw [hD]; linarith
  have hD4 : T4 ≤ D := by rw [hD]; linarith
  have hD5 : T5 ≤ D := by rw [hD]; linarith
  have hD6 : T6 ≤ D := by rw [hD]; linarith
  have hD0 : 0 ≤ D := le_trans hT1 hD1
  have hQQ : Q ≤ Q ^ 2 := by rw [sq]; exact le_mul_of_one_le_right hQ0 hQ
  have hΛ0 : 0 ≤ Q ^ 2 * Y * X := mul_nonneg (mul_nonneg (sq_nonneg Q) hY0) hX0
  have hΛ2 : Q ^ 2 * Y ≤ Q ^ 2 * Y * X :=
    le_mul_of_one_le_right (mul_nonneg (sq_nonneg Q) hY0) hX
  have hΛ1 : Q ^ 2 ≤ Q ^ 2 * Y * X :=
    (le_mul_of_one_le_right (sq_nonneg Q) hY).trans hΛ2
  have hΛ3 : Q * Y ≤ Q ^ 2 * Y * X := by
    have h0 : Q * Y ≤ Q ^ 2 * Y := mul_le_mul_of_nonneg_right hQQ (by linarith)
    linarith
  have hΛ4 : Q ≤ Q ^ 2 * Y * X := le_trans hQQ hΛ1
  have hΛ5 : Q ^ 2 * X ≤ Q ^ 2 * Y * X :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (sq_nonneg Q) hY) hX0
  set Λ := Q ^ 2 * Y * X with hΛ
  have hcQ : 0 ≤ c * Q := mul_nonneg hc hQ0
  -- P1: the thin and broad couplings
  have hP1 : (n1 + n2) * n3 ≤ (2 * c ^ 2 + 4 * c ^ 3 + 2 * c ^ 2) * (Λ * D) := by
    have hA0 : 0 ≤ 2 * (c * Q * ε + 2 * ρ * (c * Q)) + 2 * sρ := by
      have := mul_nonneg hcQ hε
      have := mul_nonneg hρ hcQ
      linarith
    have h1 := mul_le_mul (add_le_add hn1 hn2) hn3 hn3' hA0
    have e1 : (2 * (c * Q * ε + 2 * ρ * (c * Q)) + 2 * sρ) * (c * Q * E) =
        2 * c ^ 2 * (Q ^ 2 * (ε * E)) + 4 * c ^ 2 * (Q ^ 2 * (ρ * E)) +
          2 * c * (Q * (sρ * E)) := by ring
    have q1 : Q ^ 2 * (ε * E) ≤ Λ * D :=
      mul_le_mul hΛ1 (hεE.trans hD3) (mul_nonneg hε hE0) hΛ0
    have q2 : Q ^ 2 * (ρ * E) ≤ c * (Λ * D) := by
      calc Q ^ 2 * (ρ * E) ≤ Q ^ 2 * (c * Y * T5) :=
            mul_le_mul_of_nonneg_left hρE (sq_nonneg Q)
        _ = c * (Q ^ 2 * Y * T5) := by ring
        _ ≤ c * (Λ * D) := mul_le_mul_of_nonneg_left (mul_le_mul hΛ2 hD5 hT5 hΛ0) hc
    have q3 : Q * (sρ * E) ≤ c * (Λ * D) := by
      calc Q * (sρ * E) ≤ Q * (c * Y * T5) := mul_le_mul_of_nonneg_left hsρE hQ0
        _ = c * (Q * Y * T5) := by ring
        _ ≤ c * (Λ * D) := mul_le_mul_of_nonneg_left (mul_le_mul hΛ3 hD5 hT5 hΛ0) hc
    have hc2 : 0 ≤ 2 * c ^ 2 := by positivity
    have hc4 : 0 ≤ 4 * c ^ 2 := by positivity
    have hc2' : 0 ≤ 2 * c := by linarith
    calc (n1 + n2) * n3 ≤ _ := h1
      _ = _ := e1
      _ ≤ 2 * c ^ 2 * (Λ * D) + 4 * c ^ 2 * (c * (Λ * D)) + 2 * c * (c * (Λ * D)) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left q1 hc2)
            (mul_le_mul_of_nonneg_left q2 hc4)) (mul_le_mul_of_nonneg_left q3 hc2')
      _ = (2 * c ^ 2 + 4 * c ^ 3 + 2 * c ^ 2) * (Λ * D) := by ring
  -- P2: the young end
  have hP2 : n4 * n5 ≤ 4 * c ^ 2 * (Λ * D) := by
    have hB0 : 0 ≤ 2 * (c * Q * T1 + c * Q * ε) := by
      have := mul_nonneg hcQ hT1
      have := mul_nonneg hcQ hε
      linarith
    have h1 := mul_le_mul hn4 hn5 hn5' hB0
    have hs : T1 + ε ≤ 2 * D := by linarith
    calc n4 * n5 ≤ _ := h1
      _ = 2 * c ^ 2 * (Q ^ 2 * (T1 + ε)) := by ring
      _ ≤ 2 * c ^ 2 * (Λ * (2 * D)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hΛ1 hs (by linarith) hΛ0) (by positivity)
      _ = 4 * c ^ 2 * (Λ * D) := by ring
  -- P3: the old end
  have hP3 : n6 * n7 ≤ 6 * c ^ 2 * (Λ * D) := by
    have hB0 : 0 ≤ 2 * (c * Q * (T2 + ε) + c * Q * ε) := by
      have := mul_nonneg hcQ (add_nonneg hT2 hε)
      have := mul_nonneg hcQ hε
      linarith
    have h1 := mul_le_mul hn6 hn7 hn7' hB0
    have hs : T2 + ε + ε ≤ 3 * D := by linarith
    calc n6 * n7 ≤ _ := h1
      _ = 2 * c ^ 2 * (Q ^ 2 * (T2 + ε + ε)) := by ring
      _ ≤ 2 * c ^ 2 * (Λ * (3 * D)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hΛ1 hs (by linarith) hΛ0) (by positivity)
      _ = 6 * c ^ 2 * (Λ * D) := by ring
  -- P4: the transverse tail
  have hP4 : n8 * (n3 + n9) ≤ 4 * c * (Λ * D) := by
    have h1 := mul_le_mul hn8 (add_le_add hn3 hn9) (add_nonneg hn3' hn9') (by linarith)
    have hs : eD * E + eD ≤ 2 * D := by linarith
    calc n8 * (n3 + n9) ≤ _ := h1
      _ = 2 * c * (Q * (eD * E + eD)) := by ring
      _ ≤ 2 * c * (Λ * (2 * D)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hΛ4 hs (add_nonneg (mul_nonneg heD hE0) heD) hΛ0)
            (by linarith)
      _ = 4 * c * (Λ * D) := by ring
  -- P5: the bins
  have hP5 : ∑ j ∈ Finset.range N, n10 * (n11 j + n12 j) ≤ 4 * c ^ 3 * (Λ * D) := by
    have h1 : ∑ j ∈ Finset.range N, n10 * (n11 j + n12 j) ≤
        ∑ j ∈ Finset.range N, (2 * (c * Q)) * (2 * (c * Q * T4)) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have := hn11 j hj
      have := hn12 j hj
      exact mul_le_mul hn10 (by linarith) (add_nonneg (hn11' j) (hn12' j)) (by linarith)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    have h2 : (N : ℝ) * (2 * (c * Q) * (2 * (c * Q * T4))) ≤
        c * X * (2 * (c * Q) * (2 * (c * Q * T4))) :=
      mul_le_mul_of_nonneg_right hN (mul_nonneg (mul_nonneg two_pos.le hcQ)
        (mul_nonneg two_pos.le (mul_nonneg hcQ hT4)))
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ = 4 * c ^ 3 * (Q ^ 2 * X * T4) := by ring
      _ ≤ 4 * c ^ 3 * (Λ * D) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hΛ5 hD4 hT4 hΛ0)
            (mul_nonneg (by norm_num) (pow_nonneg hc 3))
  calc _ ≤ (2 * c ^ 2 + 4 * c ^ 3 + 2 * c ^ 2) * (Λ * D) + 4 * c ^ 2 * (Λ * D) +
        6 * c ^ 2 * (Λ * D) + 4 * c * (Λ * D) + 4 * c ^ 3 * (Λ * D) := by linarith
    _ = ctot c * Λ * D := by unfold ctot; ring

/-! ## The assembly -/

set_option maxHeartbeats 4000000 in
/-- **`near:deltaN`** (source 3927-3942; proof 3956-4053), from the lemmas of
`NearInst/Delta/Lemmas.lean` and the reused coefficient and masked-free statements. -/
theorem nearDeltaBoundC_of (hPart : OutPartitionSum) (hM1 : TrainMultRestr)
    (hM2 : ThinDiffMult) (hM3 : BroadMult) (hSC : RawStreamCompletion)
    (hRep : RepairCoeffBound) (hF0 : FlatFreeGainBound) (hR1 : CompactWindowBlock)
    (hR2 : PartialStripBlock) (hR3 : YoungEndResponse) (hR4 : OldEndResponse)
    (hRE : UnforcedLeray.Short.IIIa.RawCoeffEarly) (hRL : UnforcedLeray.Short.IIIa.RawCoeffLate)
    (hIn : UnforcedLeray.Short.IIIa.InletCoeffBounds)
    (hRT : UnforcedLeray.Short.IIIa.RawTransverseTail) (hFT : FlatTrainMultBound)
    (hMF : NearMaskedFreeBoundC) : NearDeltaBoundC := by
  intro P hP Kset hK hKsub mZ hmZ dm dp hdm
  have hmZ0 : 0 ≤ mZ := by linarith
  obtain ⟨K, hK1⟩ := hR1 P hP Kset hK hKsub mZ hmZ0 dm dp hdm
  refine ⟨K, ?_⟩
  intro a b δ m0 Dp ha hb hb1 hδ hm0 hm0dm hDp C0 k0 hC0 Sig hSig
  have hγ : 0 < P.eigenvalue.re := hP.eigenpair.re_pos
  have hη : 0 ≤ etaDelta P.eigenvalue.re δ := by
    unfold etaDelta
    apply mul_nonneg hγ.le
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.2 (by linarith)) (Real.cosh_pos _).le
  obtain ⟨Cp, νT, hνT, hT⟩ := hRT dm dp hdm mZ hmZ b Dp hb hDp
  obtain ⟨C1, k1, ν1, hν1, h1⟩ := hK1 a b δ Cp ha hb hb1 hδ
  obtain ⟨C2, k2, ν2, hν2, h2⟩ := hR2 P hP Kset hK hKsub mZ hmZ0 dm dp hdm a b δ ha hb hb1 hδ
  obtain ⟨C3, k3, ν3, hν3, h3⟩ := hR3 P hP Kset hK hKsub mZ hmZ0 dm dp hdm a b δ ha hb hb1 hδ
  obtain ⟨C4, k4, ν4, hν4, h4⟩ := hR4 P hP Kset hK hKsub mZ hmZ0 dm dp hdm b δ hb hb1 hδ
  obtain ⟨C5, k5, ν5, hν5, h5⟩ := hF0 P hP Kset hK hKsub mZ hmZ0 dm dp hdm
  obtain ⟨C6, k6, ν6, hν6, h6⟩ := hMF P hP Kset hK hKsub mZ hmZ0 dm dp hdm b δ hb hb1 hδ
  obtain ⟨C7, k7, ν7, hν7, h7⟩ := hFT mZ hmZ
  obtain ⟨C8, k8, ν8, hν8, h8⟩ := hSC dm dp hdm mZ hmZ
  obtain ⟨C9, k9, ν9, hν9, h9⟩ := hRE dm dp hdm mZ hmZ
  obtain ⟨C10, k10, ν10, hν10, h10⟩ := hRL dm dp hdm mZ hmZ
  obtain ⟨C11, k11, ν11, hν11, h11⟩ := hIn dm dp hdm mZ hmZ Sig P.eigenvalue P.mode hSig hP.eigenpair
  obtain ⟨ν12, hν12, h12⟩ := hRep dm dp hdm
  obtain ⟨ν13, hν13, h13⟩ := ns_rhoB_le m0 C0 dm dp k0 hC0 hm0dm
  obtain ⟨ν₀, hν₀, hν₀le⟩ := exists_pos_le_list
    [νT, ν1, ν2, ν3, ν4, ν5, ν6, ν7, ν8, ν9, ν10, ν11, ν12, ν13, 1]
    (by simp [hνT, hν1, hν2, hν3, hν4, hν5, hν6, hν7, hν8, hν9, hν10, hν11, hν12, hν13])
  obtain ⟨kk, hkk⟩ : ∃ kk : ℕ, kk = k1 + k2 + k3 + k4 + k5 + k6 + k7 + k8 + k9 + k10 + k11 :=
    ⟨_, rfl⟩
  obtain ⟨cN, hcN⟩ : ∃ cN : ℝ, cN = 4 * (a + b) * dp / δ + 2 := ⟨_, rfl⟩
  have hmax : ∀ C : ℝ, 0 ≤ max C 0 := fun C => le_max_right C 0
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = max C1 0 + max C2 0 + max C3 0 + max C4 0 + max C5 0 +
      max C6 0 + max C7 0 + max C8 0 + max C9 0 + max C10 0 + max C11 0 + (C0 + 1) + |cN| :=
    ⟨_, rfl⟩
  have hs := hmax C1; have := hmax C2; have := hmax C3; have := hmax C4; have := hmax C5
  have := hmax C6; have := hmax C7; have := hmax C8; have := hmax C9; have := hmax C10
  have := hmax C11; have := abs_nonneg cN; have := le_abs_self cN
  have hc1 : max C1 0 ≤ c := by rw [hc]; linarith
  have hc2 : max C2 0 ≤ c := by rw [hc]; linarith
  have hc3 : max C3 0 ≤ c := by rw [hc]; linarith
  have hc4 : max C4 0 ≤ c := by rw [hc]; linarith
  have hc5 : max C5 0 ≤ c := by rw [hc]; linarith
  have hc6 : max C6 0 ≤ c := by rw [hc]; linarith
  have hc7 : max C7 0 ≤ c := by rw [hc]; linarith
  have hc8 : max C8 0 ≤ c := by rw [hc]; linarith
  have hc9 : max C9 0 ≤ c := by rw [hc]; linarith
  have hc10 : max C10 0 ≤ c := by rw [hc]; linarith
  have hc11 : max C11 0 ≤ c := by rw [hc]; linarith
  have hcC0 : C0 + 1 ≤ c := by rw [hc]; linarith
  have hcN' : cN ≤ c := by rw [hc]; linarith
  have hc0 : 0 ≤ c := by linarith
  refine ⟨ctot c, 2 * kk + k0 + 1, ν₀, hν₀, ?_⟩
  intro p d hBG hpν hSg hmode S_in V rb hsplit hSin μ hμ o hact
  -- the level
  have hν := p.ν_pos
  have hε0 := p.ε_pos
  have hνle : ∀ x ∈ [νT, ν1, ν2, ν3, ν4, ν5, ν6, ν7, ν8, ν9, ν10, ν11, ν12, ν13, (1 : ℝ)],
      p.ν ≤ x := fun x hx => hpν.trans (hν₀le x hx)
  have hX : 1 ≤ p.ν⁻¹ := by
    rw [le_inv_comm₀ one_pos hν, inv_one]; exact hνle 1 (by simp)
  obtain ⟨hε1, hlog⟩ := regime_facts hBG
  have hd : dm ≤ d := hBG.dm_le
  have hdp : d ≤ dp := hBG.le_dp
  have hρ0 := ns_rhoB_pos p m0 C0 k0 hC0
  have hρ1 := h13 p d hBG (hνle ν13 (by simp))
  have hsm : 0 < p.ε ^ a := Real.rpow_pos_of_pos hε0 a
  have hsm1 : p.ε ^ a < 1 := Real.rpow_lt_one hε0.le hε1 ha
  have hS1 : 1 < p.ε ^ (-b) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hε0 hε1 (by linarith)
  have hsmS : p.ε ^ a < p.ε ^ (-b) := hsm1.trans hS1
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = p.ν⁻¹ ^ kk := ⟨_, rfl⟩
  have hQ1 : 1 ≤ Q := by rw [hQ]; exact one_le_pow₀ hX
  have hQ0 : 0 ≤ Q := by linarith
  have hcQ : 0 ≤ c * Q := mul_nonneg hc0 hQ0
  have hE1 : 1 ≤ Real.exp (etaDelta P.eigenvalue.re δ / p.ν) :=
    Real.one_le_exp (div_nonneg hη hν.le)
  have hws : ∀ pt : Chart, 0 ≤ Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt :=
    fun pt => mul_nonneg (Real.sqrt_nonneg _) (transWeight_nonneg mZ pt)
  -- the train coefficient: young, old, transverse tail, global
  have hraw : ∀ pt : Chart, ‖trainMer p.trainData pt‖ ≤
      ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt‖ +
        ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt‖ := by
    intro pt
    have h := norm_sub_le (UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt)
      (UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt)
    rwa [sub_sub_cancel] at h
  have hSCp : ∀ pt : Chart, 0 < pt.1 →
      Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
        ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt‖ ≤
          c * Q * p.ε := fun pt hpt =>
    up (h8 p d hBG (hνle ν8 (by simp)) pt hpt) hX (by omega) hε0.le hc8 hQ
  have hBY : ∀ pt ∈ ageBelow (p.ε ^ a), 0 < pt.1 →
      Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt * ‖trainMer p.trainData pt‖ ≤
        c * Q * p.ε ^ (a / 2) + c * Q * p.ε := by
    intro pt hpA hpt
    have hlt : pt.1 < p.ε ^ a := hpA
    have hE := up ((h9 p d hBG (hνle ν9 (by simp))).1 pt hpt (by linarith)) hX (by omega)
      (Real.sqrt_nonneg _) hc9 hQ
    have hsq : Real.sqrt pt.1 ≤ p.ε ^ (a / 2) := by
      calc Real.sqrt pt.1 ≤ Real.sqrt (p.ε ^ a) := Real.sqrt_le_sqrt hlt.le
        _ = p.ε ^ (a / 2) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hε0.le]; congr 1; ring
    calc Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt * ‖trainMer p.trainData pt‖
        ≤ Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
            (‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt‖ +
              ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt‖) :=
          mul_le_mul_of_nonneg_left (hraw pt) (hws pt)
      _ = Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
            ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt‖ +
          Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
            ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt‖ := by
          ring
      _ ≤ c * Q * Real.sqrt pt.1 + c * Q * p.ε := add_le_add hE (hSCp pt hpt)
      _ ≤ c * Q * p.ε ^ (a / 2) + c * Q * p.ε := by
          have := mul_le_mul_of_nonneg_left hsq hcQ
          linarith
  have hBO : ∀ pt ∈ ageAbove (p.ε ^ (-b)), 0 < pt.1 →
      Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt * ‖trainMer p.trainData pt‖ ≤
        c * Q * (p.ε ^ (b / 2) + p.ε) + c * Q * p.ε := by
    intro pt hpA hpt
    have hge : p.ε ^ (-b) ≤ pt.1 := hpA
    have hE := up ((h10 p d hBG (hνle ν10 (by simp))).1 pt (by linarith)) hX (by omega)
      (add_nonneg (Real.rpow_nonneg hpt.le _) hε0.le) hc10 hQ
    have hpow : pt.1 ^ (-1 / 2 : ℝ) ≤ p.ε ^ (b / 2) := by
      calc pt.1 ^ (-1 / 2 : ℝ) ≤ (p.ε ^ (-b)) ^ (-1 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hε0 _) hge (by norm_num)
        _ = p.ε ^ (b / 2) := by rw [← Real.rpow_mul hε0.le]; congr 1; ring
    calc Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt * ‖trainMer p.trainData pt‖
        ≤ Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
            (‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt‖ +
              ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt‖) :=
          mul_le_mul_of_nonneg_left (hraw pt) (hws pt)
      _ = Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
            ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt‖ +
          Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
            ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt‖ := by
          ring
      _ ≤ c * Q * (pt.1 ^ (-1 / 2 : ℝ) + p.ε) + c * Q * p.ε := add_le_add hE (hSCp pt hpt)
      _ ≤ c * Q * (p.ε ^ (b / 2) + p.ε) + c * Q * p.ε := by
          have := mul_le_mul_of_nonneg_left hpow hcQ
          linarith
  have hBT : ∀ pt ∈ tailSet (p.ε ^ a) (p.ε ^ (-b)) (transL Cp p.c p.ν (p.ε ^ (-b))), 0 < pt.1 →
      Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt * ‖trainMer p.trainData pt‖ ≤
        Real.exp (-Dp / p.ν) := by
    intro pt hpA hpt
    obtain ⟨_, hlt, hL⟩ := hpA
    have h := hT p d hBG (hνle νT (by simp)) pt hpt hlt hL
    have heq : ‖trainMer p.trainData pt‖ = ‖p.train.v pt.1 pt.2‖ :=
      congrArg norm (trainMer_eq p.trainData pt hpt.le)
    calc Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt * ‖trainMer p.trainData pt‖
        ≤ Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
            (‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt‖ + ‖p.train.v pt.1 pt.2‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (hws pt)
          rw [heq]
          linarith [norm_nonneg (UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt)]
      _ ≤ Real.exp (-Dp / p.ν) := h
  have hBF : ∀ pt ∈ (univ : Set Chart), 0 < pt.1 →
      Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt * ‖trainMer p.trainData pt‖ ≤
        c * Q := fun pt _ hpt =>
    up1 ((h7 p.ν ⟨hν, hνle ν7 (by simp)⟩ p.c hBG.c_eq p.trainData hBG.train_buc).2 pt hpt) hX (by omega) hc7 hQ
  -- the thin coefficient difference
  obtain ⟨z, -, hV, -, hα⟩ := hsplit.state
  have hBth : ∀ pt : Chart, 0 < pt.1 →
      Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
        ‖UnforcedLeray.Short.IIIa.chartCoeff p.R V pt - trainMer p.trainData pt‖ ≤
          c * Q * p.ε + 2 * UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 * (c * Q) := by
    intro pt hpt
    have hsplitc := chartCoeff_add_sum p.R V p.raw p.inlet (p.coord z) hV pt
    have e1 : UnforcedLeray.Short.IIIa.chartCoeff p.R V pt - trainMer p.trainData pt =
        (UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt) +
          (p.coord z 0 • UnforcedLeray.Short.IIIa.chartCoeff p.R (p.inlet 0) pt +
            p.coord z 1 • UnforcedLeray.Short.IIIa.chartCoeff p.R (p.inlet 1) pt) := by
      rw [hsplitc, Fin.sum_univ_two]; abel
    have hin : ∀ i : Fin 2, Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
        ‖UnforcedLeray.Short.IIIa.chartCoeff p.R (p.inlet i) pt‖ ≤ c * Q := fun i =>
      up1 ((h11 p d hBG (hνle ν11 (by simp)) hSg hmode i).1 pt hpt) hX (by omega) hc11 hQ
    have hn : ‖UnforcedLeray.Short.IIIa.chartCoeff p.R V pt - trainMer p.trainData pt‖ ≤
        ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt‖ +
          (|p.coord z 0| * ‖UnforcedLeray.Short.IIIa.chartCoeff p.R (p.inlet 0) pt‖ +
            |p.coord z 1| * ‖UnforcedLeray.Short.IIIa.chartCoeff p.R (p.inlet 1) pt‖) := by
      rw [e1]
      refine (norm_add_le _ _).trans (add_le_add le_rfl ((norm_add_le _ _).trans ?_))
      simp only [norm_smul, Real.norm_eq_abs, le_refl]
    have hα0 := hα 0
    have hα1 := hα 1
    have hm0' := mul_le_mul hα0 (hin 0) (mul_nonneg (hws pt) (norm_nonneg _)) hρ0.le
    have hm1' := mul_le_mul hα1 (hin 1) (mul_nonneg (hws pt) (norm_nonneg _)) hρ0.le
    calc Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
          ‖UnforcedLeray.Short.IIIa.chartCoeff p.R V pt - trainMer p.trainData pt‖
        ≤ Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
          (‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt‖ +
            (|p.coord z 0| * ‖UnforcedLeray.Short.IIIa.chartCoeff p.R (p.inlet 0) pt‖ +
              |p.coord z 1| * ‖UnforcedLeray.Short.IIIa.chartCoeff p.R (p.inlet 1) pt‖)) :=
          mul_le_mul_of_nonneg_left hn (hws pt)
      _ = Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
            ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt‖ +
          (|p.coord z 0| * (Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
              ‖UnforcedLeray.Short.IIIa.chartCoeff p.R (p.inlet 0) pt‖) +
            |p.coord z 1| * (Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
              ‖UnforcedLeray.Short.IIIa.chartCoeff p.R (p.inlet 1) pt‖)) := by ring
      _ ≤ c * Q * p.ε + (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 * (c * Q) +
            UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 * (c * Q)) :=
          add_le_add (hSCp pt hpt) (add_le_add hm0' hm1')
      _ = c * Q * p.ε + 2 * UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 * (c * Q) := by ring
  -- the bins
  have hbin : ∀ j ∈ Finset.range (binCount (p.ε ^ a) (p.ε ^ (-b)) δ),
      p.ε ^ a ≤ binEdge (p.ε ^ a) (p.ε ^ (-b)) (binCount (p.ε ^ a) (p.ε ^ (-b)) δ) j ∧
      binEdge (p.ε ^ a) (p.ε ^ (-b)) (binCount (p.ε ^ a) (p.ε ^ (-b)) δ) j <
        binEdge (p.ε ^ a) (p.ε ^ (-b)) (binCount (p.ε ^ a) (p.ε ^ (-b)) δ) (j + 1) ∧
      binEdge (p.ε ^ a) (p.ε ^ (-b)) (binCount (p.ε ^ a) (p.ε ^ (-b)) δ) (j + 1) ≤
        Real.exp (δ / 2) *
          binEdge (p.ε ^ a) (p.ε ^ (-b)) (binCount (p.ε ^ a) (p.ε ^ (-b)) δ) j ∧
      binEdge (p.ε ^ a) (p.ε ^ (-b)) (binCount (p.ε ^ a) (p.ε ^ (-b)) δ) (j + 1) ≤
        p.ε ^ (-b) := by
    intro j hj
    have hj' : j < binCount (p.ε ^ a) (p.ε ^ (-b)) δ := Finset.mem_range.1 hj
    exact ⟨binEdge_ge hsm hsmS.le _ j,
      binEdge_lt_succ hsm hsmS (binCount_pos _ _ _).ne' j,
      binEdge_succ_le hsm hsmS.le hδ j,
      binEdge_le_last hsm hsmS.le (Nat.succ_le_of_lt hj')⟩
  have hθ : p.ε ^ (1 - b / 2) ≤ p.ε ^ (1 / 50 - (K : ℝ) * (a + b)) := by
    apply Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le
    have : 0 ≤ (K : ℝ) * (a + b) := mul_nonneg (Nat.cast_nonneg K) (by linarith)
    linarith
  have hNb : (binCount (p.ε ^ a) (p.ε ^ (-b)) δ : ℝ) ≤ c * p.ν⁻¹ := by
    have h0 := binCount_lt hsm hsmS.le hδ
    have hlg : Real.log (p.ε ^ (-b) / p.ε ^ a) = (a + b) * d * p.ν⁻¹ := by
      rw [Real.log_div (Real.rpow_pos_of_pos hε0 _).ne' hsm.ne', Real.log_rpow hε0,
        Real.log_rpow hε0, hlog]
      ring
    rw [hlg] at h0
    have h1 : 4 * ((a + b) * d * p.ν⁻¹) / δ ≤ 4 * (a + b) * dp / δ * p.ν⁻¹ := by
      have e1 : 4 * ((a + b) * d * p.ν⁻¹) / δ = 4 * (a + b) * d / δ * p.ν⁻¹ := by ring
      rw [e1]
      have hab : 0 ≤ 4 * (a + b) := by linarith
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdp hab) hδ.le) (by linarith)
    have h2 : cN * p.ν⁻¹ ≤ c * p.ν⁻¹ := mul_le_mul_of_nonneg_right hcN' (by linarith)
    have h3 : (2 : ℝ) ≤ 2 * p.ν⁻¹ := by linarith
    have h4 : cN * p.ν⁻¹ = 4 * (a + b) * dp / δ * p.ν⁻¹ + 2 * p.ν⁻¹ := by rw [hcN]; ring
    linarith
  -- ρ_b terms
  obtain ⟨hρE, hsρE⟩ := rhoB_E_le hBG (m0 := m0) (η := etaDelta P.eigenvalue.re δ) k0
    (by linarith [show 3 * dm / 11 ≤ 3 * d / 11 by linarith]) hC0 hX
  have hY1 : 1 ≤ p.ν⁻¹ ^ k0 := one_le_pow₀ hX
  have hT5n : 0 ≤ p.ε ^ (3 / 22 : ℝ) * Real.exp ((etaDelta P.eigenvalue.re δ + m0 / 2) / p.ν) :=
    mul_nonneg (Real.rpow_nonneg hε0.le _) (Real.exp_pos _).le
  have hρE' : UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 *
      Real.exp (etaDelta P.eigenvalue.re δ / p.ν) ≤ c * p.ν⁻¹ ^ k0 *
        (p.ε ^ (3 / 22 : ℝ) * Real.exp ((etaDelta P.eigenvalue.re δ + m0 / 2) / p.ν)) :=
    hρE.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcC0 (by linarith)) hT5n)
  have hsρE' : Real.sqrt (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) *
      Real.exp (etaDelta P.eigenvalue.re δ / p.ν) ≤ c * p.ν⁻¹ ^ k0 *
        (p.ε ^ (3 / 22 : ℝ) * Real.exp ((etaDelta P.eigenvalue.re δ + m0 / 2) / p.ν)) :=
    hsρE.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcC0 (by linarith)) hT5n)
  -- the exponentials
  have hm0E : Real.exp (etaDelta P.eigenvalue.re δ / p.ν) ≤
      Real.exp ((m0 + etaDelta P.eigenvalue.re δ) / p.ν) := by
    apply Real.exp_le_exp.2
    apply div_le_div_of_nonneg_right _ hν.le
    linarith
  have hεE : p.ε * Real.exp (etaDelta P.eigenvalue.re δ / p.ν) ≤
      p.ε * Real.exp ((m0 + etaDelta P.eigenvalue.re δ) / p.ν) :=
    mul_le_mul_of_nonneg_left hm0E hε0.le
  have hε3 : p.ε ≤ p.ε * Real.exp ((m0 + etaDelta P.eigenvalue.re δ) / p.ν) := by
    exact le_mul_of_one_le_right hε0.le
      (Real.one_le_exp (div_nonneg (by linarith : 0 ≤ m0 + etaDelta P.eigenvalue.re δ) hν.le))
  have heDE : Real.exp (-Dp / p.ν) * Real.exp (etaDelta P.eigenvalue.re δ / p.ν) ≤
      Real.exp (-(Dp - etaDelta P.eigenvalue.re δ) / p.ν) := by
    rw [← Real.exp_add]
    apply le_of_eq
    congr 1
    ring
  have heD6 : Real.exp (-Dp / p.ν) ≤ Real.exp (-(Dp - etaDelta P.eigenvalue.re δ) / p.ν) := by
    apply Real.exp_le_exp.2
    apply div_le_div_of_nonneg_right _ hν.le
    linarith
  -- the operator bound
  refine (ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (deltaN_apply_le hPart P.eigenvalue.re p.ν_pos o (transL Cp p.c p.ν (p.ε ^ (-b))) hsm hsmS
      hδ)).trans ?_
  have hfin : ctot c * (Q ^ 2 * p.ν⁻¹ ^ k0 * p.ν⁻¹) *
      deltaNRhs a b K (etaDelta P.eigenvalue.re δ) m0 Dp p.ε p.ν =
      ctot c * p.ν⁻¹ ^ (2 * kk + k0 + 1) *
        deltaNRhs a b K (etaDelta P.eigenvalue.re δ) m0 Dp p.ε p.ν := by
    rw [hQ]; ring
  rw [← hfin]
  refine combine hQ1 hY1 hX hE1 hc0 hε0.le hρ0.le (Real.sqrt_nonneg _) (Real.exp_pos _).le
    (Real.rpow_nonneg hε0.le _) (Real.rpow_nonneg hε0.le _)
    (mul_nonneg hε0.le (Real.exp_pos _).le)
    (mul_nonneg (Real.rpow_nonneg hε0.le _) (Real.exp_pos _).le) hT5n (Real.exp_pos _).le rfl
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hNb hεE hε3 hρE' hsρE' heDE heD6
  -- n1: thin coupling
  · have h := hM2 p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) P.eigenvalue.re p.ν p.R
      p.ν_pos p.trainData V rb o.M0 o.MU _ p.c_pos
      (add_nonneg (mul_nonneg hcQ hε0.le) (mul_nonneg (mul_nonneg two_pos.le hρ0.le) hcQ))
      hact.flat hact.split hBth
    linarith
  -- n2: broad coupling
  · exact hM3 p.c mZ _ P.eigenvalue.re p.ν p.R p.ν_pos p.trainData V rb o.M0 o.MU p.c_pos hρ0
      hact.flat hact.split (h12 p d hBG (hνle ν12 (by simp)) _ S_in V rb hsplit)
  -- n3: masked free bound
  · exact up (h6 p d hBG (hνle ν6 (by simp)) _ hρ0 hρ1 μ hμ o.SN hact.near) hX (by omega)
      (Real.exp_pos _).le hc6 hQ
  -- n4: young train multiplier
  · exact hM1 p.c mZ _ P.eigenvalue.re p.ν p.ν_pos p.trainData o.M0 (ageBelow (p.ε ^ a)) _
      p.c_pos (measurableSet_ageBelow _)
      (add_nonneg (mul_nonneg hcQ (Real.rpow_nonneg hε0.le _)) (mul_nonneg hcQ hε0.le))
      hact.flat hBY
  -- n5: young response
  · exact up1 (h3 p d hBG (hνle ν3 (by simp)) _ hρ0 hρ1 μ hμ o.SN o.S0 hact.near hact.free) hX
      (by omega) hc3 hQ
  -- n6: old train multiplier
  · exact hM1 p.c mZ _ P.eigenvalue.re p.ν p.ν_pos p.trainData o.M0 (ageAbove (p.ε ^ (-b))) _
      p.c_pos (measurableSet_ageAbove _)
      (add_nonneg (mul_nonneg hcQ (add_nonneg (Real.rpow_nonneg hε0.le _) hε0.le))
        (mul_nonneg hcQ hε0.le))
      hact.flat hBO
  -- n7: old response
  · exact up1 (h4 p d hBG (hνle ν4 (by simp)) _ hρ0 hρ1 μ hμ o.SN o.S0 hact.near hact.free) hX
      (by omega) hc4 hQ
  -- n8: transverse tail multiplier
  · exact hM1 p.c mZ _ P.eigenvalue.re p.ν p.ν_pos p.trainData o.M0
      (tailSet (p.ε ^ a) (p.ε ^ (-b)) (transL Cp p.c p.ν (p.ε ^ (-b)))) _ p.c_pos
      (measurableSet_tailSet _ _ _) (Real.exp_pos _).le hact.flat hBT
  -- n9: flat free gain bound
  · exact up1 (h5 p d hBG (hνle ν5 (by simp)) _ hρ0 hρ1 μ hμ o.S0 hact.free) hX (by omega) hc5 hQ
  -- n10: global train multiplier
  · have h := hM1 p.c mZ _ P.eigenvalue.re p.ν p.ν_pos p.trainData o.M0 univ _ p.c_pos
      MeasurableSet.univ hcQ hact.flat hBF
    rwa [gainRestrM_univ] at h
  -- n11: complete blocks
  · intro j hj
    obtain ⟨hl, hlr, hr, hrS⟩ := hbin j hj
    exact up (h1 p d hBG (hνle ν1 (by simp)) _ hρ0 hρ1 μ hμ o.SN o.S0 hact.near hact.free _ _
      hl hlr hr hrS) hX (by omega)
      (mul_nonneg (Real.rpow_nonneg hε0.le _) (Real.exp_pos _).le) hc1 hQ
  -- n12: partial strips
  · intro j hj
    obtain ⟨hl, hlr, hr, hrS⟩ := hbin j hj
    have h := up (h2 p d hBG (hνle ν2 (by simp)) _ hρ0 hρ1 μ hμ o.SN o.S0 hact.near hact.free _ _
      (transL Cp p.c p.ν (p.ε ^ (-b))) hl hlr hr hrS) hX (by omega)
      (mul_nonneg (Real.rpow_nonneg hε0.le _) (Real.exp_pos _).le) hc2 hQ
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hcQ)
    exact mul_le_mul_of_nonneg_right hθ (Real.exp_pos _).le

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
