import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_1

/-!
# Raised-stream bound (`PartIII-b:C/rep/8/2/1/1/2`)

Source `the November 2 reference manuscript` lines 2075-2077, 5464-5465.
With `F = trainFpsi L` (`F(σ,(ξ,η)) = ψ(e^σ,(ξ,η))`, `σ = log s`), the raised stream
`H = ψ - η∂_ηψ - 2s∂_sψ` is `F - η∂_2F - 2∂_1F` at `(log s,(q,η))`, since `s∂_s = ∂_σ`.
Its absolute value is at most `3𝔴₃` because `𝔴₃` controls the order-`≤1` jets of `F`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The derivative in the last variable of `u ↦ F(σ,(q,u))`. -/
theorem ringRaised_dEta {F : ℝ × (ℝ × ℝ) → ℝ} (hF : Differentiable ℝ F) (σ q t : ℝ) :
    deriv (fun u : ℝ => F (σ, (q, u))) t = fderiv ℝ F (σ, (q, t)) (0, (0, 1)) := by
  have hg : HasDerivAt (fun u : ℝ => ((σ, (q, u)) : ℝ × (ℝ × ℝ))) ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) t :=
    (hasDerivAt_const t σ).prodMk ((hasDerivAt_const t q).prodMk (hasDerivAt_id t))
  have hl : HasFDerivAt F (fderiv ℝ F (σ, (q, t))) (σ, (q, t)) := (hF _).hasFDerivAt
  have h : deriv (fun u : ℝ => F (σ, (q, u))) t = fderiv ℝ F (σ, (q, t)) (0, (0, 1)) :=
    (hl.comp_hasDerivAt t hg).deriv
  exact h

/-- `s ∂_s [F(log s,(q,η))] = ∂_σ F` at `s > 0`. -/
theorem ringRaised_dS {F : ℝ × (ℝ × ℝ) → ℝ} (hF : Differentiable ℝ F) {s : ℝ} (hs : 0 < s)
    (q η : ℝ) :
    s * deriv (fun u : ℝ => F (Real.log u, (q, η))) s =
      fderiv ℝ F (Real.log s, (q, η)) (1, (0, 0)) := by
  have hg : HasDerivAt (fun u : ℝ => ((Real.log u, (q, η)) : ℝ × (ℝ × ℝ)))
      ((s⁻¹ : ℝ), ((0 : ℝ), (0 : ℝ))) s :=
    (Real.hasDerivAt_log hs.ne').prodMk ((hasDerivAt_const s q).prodMk (hasDerivAt_const s η))
  have hl : HasFDerivAt F (fderiv ℝ F (Real.log s, (q, η))) (Real.log s, (q, η)) :=
    (hF _).hasFDerivAt
  have h : deriv (fun u : ℝ => F (Real.log u, (q, η))) s =
      fderiv ℝ F (Real.log s, (q, η)) ((s⁻¹ : ℝ), ((0 : ℝ), (0 : ℝ))) :=
    (hl.comp_hasDerivAt s hg).deriv
  have hw : ((s⁻¹ : ℝ), ((0 : ℝ), (0 : ℝ))) = s⁻¹ • ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) := by
    simp
  rw [h, hw, map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]

/-- The raised stream in terms of the dilation-variable jets of `F = trainFpsi L`. -/
theorem ringRaised_stream_eq (L : ReturnLevel) (hF : Differentiable ℝ (trainFpsi L))
    {s : ℝ} (hs : 0 < s) (q η : ℝ) :
    UnforcedLeray.Cons.C03.raisedStream L.train.ψ s q η =
      trainFpsi L (Real.log s, (q, η)) -
        (η * fderiv ℝ (trainFpsi L) (Real.log s, (q, η)) (0, (0, 1)) +
          2 * fderiv ℝ (trainFpsi L) (Real.log s, (q, η)) (1, (0, 0))) := by
  have hψ : ∀ t : ℝ, 0 < t → ∀ z : ℝ × ℝ, L.train.ψ t z = trainFpsi L (Real.log t, z) := by
    intro t ht z
    unfold trainFpsi
    rw [Real.exp_log ht]
  have hA : L.train.ψ s (q, η) = trainFpsi L (Real.log s, (q, η)) := hψ s hs _
  have hB : deriv (fun t => L.train.ψ s (q, t)) η =
      fderiv ℝ (trainFpsi L) (Real.log s, (q, η)) (0, (0, 1)) := by
    have hfun : (fun t => L.train.ψ s (q, t)) = fun t => trainFpsi L (Real.log s, (q, t)) :=
      funext fun t => hψ s hs _
    rw [hfun]
    exact ringRaised_dEta hF (Real.log s) q η
  have hC : s * deriv (fun t => L.train.ψ t (q, η)) s =
      fderiv ℝ (trainFpsi L) (Real.log s, (q, η)) (1, (0, 0)) := by
    have hev : (fun t => L.train.ψ t (q, η)) =ᶠ[𝓝 s]
        (fun t => trainFpsi L (Real.log t, (q, η))) := by
      filter_upwards [Ioi_mem_nhds hs] with t ht
      exact hψ t ht _
    rw [hev.deriv_eq]
    exact ringRaised_dS hF hs q η
  have key : ∀ X : ℝ, 2 * s * X = 2 * (s * X) := fun X => by ring
  unfold UnforcedLeray.Cons.C03.raisedStream
  rw [hA, hB, key, hC]

/-- `|T w| ≤ ‖T‖` for `‖w‖ ≤ 1`. -/
theorem ringRaised_apply_le (T : ℝ × (ℝ × ℝ) →L[ℝ] ℝ) (w : ℝ × (ℝ × ℝ)) (hw : ‖w‖ ≤ 1) :
    |T w| ≤ ‖T‖ := by
  rw [← Real.norm_eq_abs]
  calc ‖T w‖ ≤ ‖T‖ * ‖w‖ := T.le_opNorm w
    _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _ = ‖T‖ := mul_one _

/-- The dilation-variable jet weight summand at order `j`, at `z`. -/
def ringFj (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) (j : ℕ) : ℝ :=
  ‖iteratedFDeriv ℝ j (trainFv L) z‖ + ‖iteratedFDeriv ℝ j (trainFp L) z‖ +
    ‖iteratedFDeriv ℝ j (trainFpsi L) z‖

/-- **The raised-stream bound** (source 2075-2077, 5464-5465). -/
theorem raisedStreamBound : RaisedStreamBound := by
  intro L hFc p hp
  obtain ⟨s, q, η⟩ := p
  dsimp only at hp ⊢
  have hs : 0 < s := hp
  have hF : Differentiable ℝ (trainFpsi L) := hFc.differentiable (by simp)
  rw [ringRaised_stream_eq L hF hs q η]
  have hW : trainWeight 3 L (s, (q, η)) = (1 + |η|) ^ 3 * ∑ j ∈ Finset.range 5, ringFj L (Real.log s, (q, η)) j :=
    rfl
  rw [hW]
  -- the norms of the jets at the chart point
  have hFz : |trainFpsi L (Real.log s, (q, η))| =
      ‖iteratedFDeriv ℝ 0 (trainFpsi L) (Real.log s, (q, η))‖ := by
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  have hB0 : ‖iteratedFDeriv ℝ 1 (trainFpsi L) (Real.log s, (q, η))‖ =
      ‖fderiv ℝ (trainFpsi L) (Real.log s, (q, η))‖ := by
    rw [norm_iteratedFDeriv_one]
  have hw1 : ‖((0 : ℝ), ((0 : ℝ), (1 : ℝ)))‖ ≤ 1 := by
    simp [Prod.norm_def]
  have hw2 : ‖((1 : ℝ), ((0 : ℝ), (0 : ℝ)))‖ ≤ 1 := by
    simp [Prod.norm_def]
  have hD1 := ringRaised_apply_le (fderiv ℝ (trainFpsi L) (Real.log s, (q, η)))
    ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) hw1
  have hD2 := ringRaised_apply_le (fderiv ℝ (trainFpsi L) (Real.log s, (q, η)))
    ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) hw2
  set A := ‖iteratedFDeriv ℝ 0 (trainFpsi L) (Real.log s, (q, η))‖ with hAdef
  set B := ‖iteratedFDeriv ℝ 1 (trainFpsi L) (Real.log s, (q, η))‖ with hBdef
  set Dz := fderiv ℝ (trainFpsi L) (Real.log s, (q, η)) with hDdef
  set S := ∑ j ∈ Finset.range 5, ringFj L (Real.log s, (q, η)) j with hSdef
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0' : 0 ≤ B := norm_nonneg _
  have hBD : B = ‖Dz‖ := hB0
  -- the sum dominates the order-0 and order-1 trainFpsi jets
  have hsum : ringFj L (Real.log s, (q, η)) 0 + ringFj L (Real.log s, (q, η)) 1 ≤ S := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (f := ringFj L (Real.log s, (q, η)))
      (show ({0, 1} : Finset ℕ) ⊆ Finset.range 5 by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        simp only [Finset.mem_range]
        omega)
      (fun j _ _ => by unfold ringFj; positivity)
    rwa [Finset.sum_pair (show (0 : ℕ) ≠ 1 by norm_num)] at h
  have h0 : A ≤ ringFj L (Real.log s, (q, η)) 0 := by
    unfold ringFj
    linarith [norm_nonneg (iteratedFDeriv ℝ 0 (trainFv L) (Real.log s, (q, η))),
      norm_nonneg (iteratedFDeriv ℝ 0 (trainFp L) (Real.log s, (q, η)))]
  have h1 : B ≤ ringFj L (Real.log s, (q, η)) 1 := by
    unfold ringFj
    linarith [norm_nonneg (iteratedFDeriv ℝ 1 (trainFv L) (Real.log s, (q, η))),
      norm_nonneg (iteratedFDeriv ℝ 1 (trainFp L) (Real.log s, (q, η)))]
  have hAB : A + B ≤ S := by linarith
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => by unfold ringFj; positivity
  -- the two product terms
  have e1 : |η * Dz (0, (0, 1))| ≤ |η| * B := by
    rw [abs_mul, hBD]
    exact mul_le_mul_of_nonneg_left hD1 (abs_nonneg η)
  have e2 : |2 * Dz (1, (0, 0))| ≤ 2 * B := by
    rw [abs_mul, abs_two, hBD]
    exact mul_le_mul_of_nonneg_left hD2 (by norm_num)
  have hfin1 : |trainFpsi L (Real.log s, (q, η)) - (η * Dz (0, (0, 1)) + 2 * Dz (1, (0, 0)))| ≤
      A + |η| * B + 2 * B := by
    have hFz' := abs_le.mp (le_of_eq hFz)
    have e1' := abs_le.mp e1
    have e2' := abs_le.mp e2
    have hFa : |trainFpsi L (Real.log s, (q, η))| ≤ A := le_of_eq hFz
    have hFb := abs_le.mp hFa
    exact abs_le.mpr ⟨by linarith [hFb.1, e1'.1, e2'.1], by linarith [hFb.2, e1'.2, e2'.2]⟩
  have hx1 : (1 : ℝ) ≤ 1 + |η| := by linarith [abs_nonneg η]
  have hx3 : (1 + |η|) ≤ (1 + |η|) ^ 3 := le_self_pow₀ hx1 (by norm_num)
  have hmid : (1 + |η|) * (A + B) ≤ (1 + |η|) ^ 3 * S :=
    calc (1 + |η|) * (A + B) ≤ (1 + |η|) * S := mul_le_mul_of_nonneg_left hAB (by linarith)
      _ ≤ (1 + |η|) ^ 3 * S := mul_le_mul_of_nonneg_right hx3 hS0
  have hbig : A + |η| * B + 2 * B ≤ 3 * ((1 + |η|) ^ 3 * S) := by
    nlinarith [mul_nonneg (abs_nonneg η) hA0, mul_nonneg (abs_nonneg η) hB0']
  linarith [hfin1, hbig]

end UnforcedLeray.Short.PartIIIb.Concrete

end
