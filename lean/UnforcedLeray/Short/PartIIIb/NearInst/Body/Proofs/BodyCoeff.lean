import UnforcedLeray.Short.PartIIIb.NearInst.Body.Forced
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.NearSolver

/-!
Proof of `BodyCoeffColumn` (source 4032-4036: thin difference `P_ν ε e^{m₀/ν}`, stream completion
and entrance adjustment; 4045-4049 and 2766-2769: broad `2√ρ_b`; 4116-4118: `g⁻¹ ≤ 1`).
Route: `G⁻¹(M_U - M_0)x = G⁻¹fst(M_U-M_0)g w + G⁻¹snd(M_U-M_0)g w`, `w = g⁻¹x`; the thin part by
`Delta.ThinDiffMult` with the block `hBth` of `Delta/Assembly.lean`, the broad part by
`Delta.BroadMult`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Body

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0223
open UnforcedLeray.B0220 (HSpace measureH Profile)

theorem bc_exists_pos_le_list :
    ∀ l : List ℝ, (∀ x ∈ l, 0 < x) → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ x ∈ l, ν₀ ≤ x
  | [], _ => ⟨1, one_pos, by simp⟩
  | x :: l, h => by
    obtain ⟨m, hm, hle⟩ := bc_exists_pos_le_list l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    refine ⟨min x m, lt_min (h x (by simp)) hm, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hle y hy)

theorem bc_up {x C t X Q c : ℝ} {k kk : ℕ} (h : x ≤ C * X ^ k * t) (hX : 1 ≤ X) (hk : k ≤ kk)
    (ht : 0 ≤ t) (hc : max C 0 ≤ c) (hQ : Q = X ^ kk) : x ≤ c * Q * t := by
  have h1 : C * X ^ k ≤ c * X ^ kk :=
    mul_le_mul ((le_max_left C 0).trans hc) (pow_le_pow_right₀ hX hk)
      (pow_nonneg (by linarith) _) ((le_max_right C 0).trans hc)
  rw [hQ]
  exact h.trans (mul_le_mul_of_nonneg_right h1 ht)

theorem bc_up1 {x C X Q c : ℝ} {k kk : ℕ} (h : x ≤ C * X ^ k) (hX : 1 ≤ X) (hk : k ≤ kk)
    (hc : max C 0 ≤ c) (hQ : Q = X ^ kk) : x ≤ c * Q := by
  rw [hQ]
  exact h.trans (mul_le_mul ((le_max_left C 0).trans hc) (pow_le_pow_right₀ hX hk)
    (pow_nonneg (by linarith) _) ((le_max_right C 0).trans hc))

theorem bc_transWeight_nonneg (mZ : ℝ) (p : Chart) :
    0 ≤ UnforcedLeray.Short.IIIa.transWeight mZ p := by
  unfold UnforcedLeray.Short.IIIa.transWeight
  positivity

set_option maxHeartbeats 1600000 in
theorem bodyCoeffColumn_of (hM2 : Delta.ThinDiffMult) (hM3 : Delta.BroadMult)
    (hSC : Delta.RawStreamCompletion) (hRep : Delta.RepairCoeffBound)
    (hIn : UnforcedLeray.Short.IIIa.InletCoeffBounds) (hG : GainInvContract) :
    BodyCoeffColumn := by
  intro dm dp hdm mZ hmZ m0 C0 k0 hC0 Sig lam q hSig hq
  obtain ⟨C8, k8, ν8, hν8, h8⟩ := hSC dm dp hdm mZ hmZ
  obtain ⟨C11, k11, ν11, hν11, h11⟩ := hIn dm dp hdm mZ hmZ Sig lam q hSig hq
  obtain ⟨ν12, hν12, h12⟩ := hRep dm dp hdm
  obtain ⟨ν₀, hν₀, hν₀le⟩ := bc_exists_pos_le_list [ν8, ν11, ν12, 1]
    (by simp [hν8, hν11, hν12])
  obtain ⟨kk, hkk⟩ : ∃ kk : ℕ, kk = k8 + k11 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = max C8 0 + max C11 0 + 1 := ⟨_, rfl⟩
  have hs8 := le_max_right C8 0
  have hs11 := le_max_right C11 0
  have hc8 : max C8 0 ≤ c := by rw [hc]; linarith
  have hc11 : max C11 0 ≤ c := by rw [hc]; linarith
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  refine ⟨4 * c + 2, kk, ν₀, hν₀, ?_⟩
  intro p d hBG hpν hSg hmode S_in V rb hsplit γ hγ M0 MU hM0 hMU x
  have hν := p.ν_pos
  have hε0 := p.ε_pos
  have hνle : ∀ y ∈ [ν8, ν11, ν12, (1 : ℝ)], p.ν ≤ y := fun y hy => hpν.trans (hν₀le y hy)
  have hX : 1 ≤ p.ν⁻¹ := by
    rw [le_inv_comm₀ one_pos hν, inv_one]; exact hνle 1 (by simp)
  have hρ0 := ns_rhoB_pos p m0 C0 k0 hC0
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = p.ν⁻¹ ^ kk := ⟨_, rfl⟩
  have hQ1 : 1 ≤ Q := by rw [hQ]; exact one_le_pow₀ hX
  have hQ0 : 0 ≤ Q := by linarith
  have hcQ : 0 ≤ c * Q := mul_nonneg hc0 hQ0
  have hws : ∀ pt : Chart, 0 ≤ Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt :=
    fun pt => mul_nonneg (Real.sqrt_nonneg _) (bc_transWeight_nonneg mZ pt)
  have hSCp : ∀ pt : Chart, 0 < pt.1 →
      Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
        ‖UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt‖ ≤
          c * Q * p.ε := fun pt hpt =>
    bc_up (h8 p d hBG (hνle ν8 (by simp)) pt hpt) hX (by omega) hε0.le hc8 hQ
  obtain ⟨z, -, hV, -, hα⟩ := hsplit.state
  have hBth : ∀ pt : Chart, 0 < pt.1 →
      Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
        ‖UnforcedLeray.Short.IIIa.chartCoeff p.R V pt - trainMer p.trainData pt‖ ≤
          c * Q * p.ε + 2 * UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 * (c * Q) := by
    intro pt hpt
    have hsplitc := Delta.chartCoeff_add_sum p.R V p.raw p.inlet (p.coord z) hV pt
    have e1 : UnforcedLeray.Short.IIIa.chartCoeff p.R V pt - trainMer p.trainData pt =
        (UnforcedLeray.Short.IIIa.chartCoeff p.R p.raw pt - trainMer p.trainData pt) +
          (p.coord z 0 • UnforcedLeray.Short.IIIa.chartCoeff p.R (p.inlet 0) pt +
            p.coord z 1 • UnforcedLeray.Short.IIIa.chartCoeff p.R (p.inlet 1) pt) := by
      rw [hsplitc, Fin.sum_univ_two]; abel
    have hin : ∀ i : Fin 2, Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
        ‖UnforcedLeray.Short.IIIa.chartCoeff p.R (p.inlet i) pt‖ ≤ c * Q := fun i =>
      bc_up1 ((h11 p d hBG (hνle ν11 (by simp)) hSg hmode i).1 pt hpt) hX (by omega) hc11 hQ
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
  -- the thin and broad parts
  have hB : 0 ≤ c * Q * p.ε + 2 * UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 * (c * Q) :=
    add_nonneg (mul_nonneg hcQ hε0.le) (mul_nonneg (mul_nonneg two_pos.le hρ0.le) hcQ)
  have hthin := hM2 p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) γ p.ν p.R
    p.ν_pos p.trainData V rb M0 MU _ p.c_pos hB hM0 hMU hBth
  have hbroad := hM3 p.c mZ _ γ p.ν p.R p.ν_pos p.trainData V rb M0 MU p.c_pos hρ0
    hM0 hMU (h12 p d hBG (hνle ν12 (by simp)) _ S_in V rb hsplit)
  obtain ⟨w, hw⟩ : ∃ w, w = (gainH p.c γ p.ν_pos).symm x := ⟨_, rfl⟩
  have hwx : ‖w‖ ≤ ‖x‖ := by
    rw [hw]; exact (hG p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) γ p.ν p.ν_pos hγ).1 x
  have hgw : gainH p.c γ p.ν_pos w = x := by rw [hw]; exact (gainH p.c γ p.ν_pos).apply_symm_apply x
  have hsplit2 : (gainEquiv p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) γ p.ν_pos).symm ((MU - M0) x) =
      Delta.gainConjM γ p.ν_pos (Delta.fstZ p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) ∘L (MU - M0)) w +
        Delta.gainConjM γ p.ν_pos (Delta.sndZ p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) ∘L (MU - M0)) w := by
    rw [Delta.gainConjM_apply, Delta.gainConjM_apply, hgw]
    simp only [ContinuousLinearMap.comp_apply]
    rw [← map_add, Delta.fstZ_add_sndZ]
  have h1 : ‖Delta.gainConjM γ p.ν_pos (Delta.fstZ p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) ∘L (MU - M0)) w‖ ≤
      2 * (c * Q * p.ε + 2 * (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) * (c * Q)) * ‖x‖ :=
    ((Delta.gainConjM γ p.ν_pos (Delta.fstZ p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) ∘L (MU - M0))).le_opNorm w).trans
      (mul_le_mul hthin hwx (norm_nonneg _) (by linarith))
  have h2 : ‖Delta.gainConjM γ p.ν_pos (Delta.sndZ p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) ∘L (MU - M0)) w‖ ≤
      2 * Real.sqrt (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) * ‖x‖ :=
    ((Delta.gainConjM γ p.ν_pos (Delta.sndZ p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) ∘L (MU - M0))).le_opNorm w).trans
      (mul_le_mul hbroad hwx (norm_nonneg _) (by positivity))
  have hsq := Real.sqrt_nonneg (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0)
  have hQk : p.ν⁻¹ ^ kk = Q := hQ.symm
  rw [hsplit2, hQk]
  refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
  have hx0 := norm_nonneg x
  have hfin : 2 * (c * Q * p.ε + 2 * (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) * (c * Q)) + 2 * Real.sqrt (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) ≤
      (4 * c + 2) * Q * (p.ε + (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) + Real.sqrt (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0)) := by
    nlinarith [mul_nonneg hcQ hε0.le, mul_nonneg hcQ hρ0.le, mul_nonneg hQ0 hsq,
      mul_nonneg hc0 (mul_nonneg hQ0 hsq), mul_le_mul_of_nonneg_right hQ1 hsq]
  nlinarith [mul_le_mul_of_nonneg_right hfin hx0]

end UnforcedLeray.Short.PartIIIb.NearInst.Body
