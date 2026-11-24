import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.FlatOrthSwap.Calc

/-!
# Helper for `PartIII-a:T18/2/4/4` (`FlatOrthSwap`): the slice test fields `Ψ¹ = -∂_sΦ - νΔΦ`, `Ψ² = Φ`

For a divergence-free space-time test field `Φ` (`IsFlatTest`), the slices `Ψ¹(s) , Ψ²(s)` are
`IsDivFreeTestField` for every `s`: smooth and `c`-periodic in `q`, `η`-compact, and
`div_x Ψ¹(s) = 0` (commutation of `∂_s` and `Δ` with the divergence, `Calc.alg_div_fos`).
No `sorry`, no axioms.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.FOS

/-- The `i`-th component of a space-time field as a function on `V3`. -/
def gI (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (i : Fin 2) : V3 → ℝ := fun p => Φ p.1 p.2 i

/-- The slice operator on `V3`: `-∂_sΦ_i - νΔΦ_i` with coefficients `(-1)`, `(-ν)`. -/
def Psi3 (ν : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (i : Fin 2) : V3 → ℝ :=
  fun q => (-1) * Dv eT (gI Φ i) q + (-ν) * (Dv eQ (Dv eQ (gI Φ i)) q + Dv eH (Dv eH (gI Φ i)) q)

/-- `Ψ¹_i(s,x) = -∂_sΦ_i(s,x) - νΔ_xΦ_i(s,x)`. -/
def psi1 (ν : ℝ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (s : ℝ) (x : ℝ × ℝ) (i : Fin 2) : ℝ :=
  (-1) * flatDt Φ s x i + (-ν) * flatLap Φ s x i

lemma flatDt_eq_fos {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : ∀ i, ContDiff ℝ ∞ (gI Φ i))
    (s : ℝ) (x : ℝ × ℝ) (i : Fin 2) :
    flatDt Φ s x i = Dv eT (gI Φ i) (s, x) :=
  deriv_time_fos (differentiable_fos (hΦ i)) s x

lemma flatLap_eq_fos {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : ∀ i, ContDiff ℝ ∞ (gI Φ i))
    (s : ℝ) (x : ℝ × ℝ) (i : Fin 2) :
    flatLap Φ s x i = Dv eQ (Dv eQ (gI Φ i)) (s, x) + Dv eH (Dv eH (gI Φ i)) (s, x) :=
  lapP_slice (hΦ i) s x

lemma psi1_eq_fos {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : ∀ i, ContDiff ℝ ∞ (gI Φ i))
    (ν : ℝ) (s : ℝ) (x : ℝ × ℝ) (i : Fin 2) :
    psi1 ν Φ s x i = Psi3 ν Φ i (s, x) := by
  simp only [psi1, Psi3]
  rw [flatDt_eq_fos hΦ, flatLap_eq_fos hΦ]

lemma psi3_contDiff {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : ∀ i, ContDiff ℝ ∞ (gI Φ i))
    (ν : ℝ) (i : Fin 2) : ContDiff ℝ ∞ (Psi3 ν Φ i) := by
  unfold Psi3
  exact (contDiff_const.mul (contDiff_Dv (hΦ i) eT)).add
    (contDiff_const.mul ((contDiff_Dv (contDiff_Dv (hΦ i) eQ) eQ).add
      (contDiff_Dv (contDiff_Dv (hΦ i) eH) eH)))

lemma psi1_contDiff_x {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : ∀ i, ContDiff ℝ ∞ (gI Φ i))
    (ν : ℝ) (s : ℝ) (i : Fin 2) :
    ContDiff ℝ ∞ (fun x : ℝ × ℝ => psi1 ν Φ s x i) := by
  have e : (fun x : ℝ × ℝ => psi1 ν Φ s x i) = fun x => Psi3 ν Φ i (s, x) :=
    funext fun x => psi1_eq_fos hΦ ν s x i
  rw [e]
  exact (psi3_contDiff hΦ ν i).comp ((contDiff_const (c := s)).prodMk contDiff_id)

lemma continuous_psi1 {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : ∀ i, ContDiff ℝ ∞ (gI Φ i))
    (ν : ℝ) (i : Fin 2) : Continuous fun p : V3 => psi1 ν Φ p.1 p.2 i := by
  have e : (fun p : V3 => psi1 ν Φ p.1 p.2 i) = Psi3 ν Φ i :=
    funext fun p => psi1_eq_fos hΦ ν p.1 p.2 i
  rw [e]
  exact (psi3_contDiff hΦ ν i).continuous

lemma lapP_periodic {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) (x : ℝ × ℝ) :
    lapP φ (x.1 + c, x.2) = lapP φ x := by
  unfold lapP
  rw [((hφ.pd 0).pd 0).periodic x, ((hφ.pd 1).pd 1).periodic x]

lemma flatLap_periodic {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} {c : ℝ} (s : ℝ) (i : Fin 2)
    (hψ : B0579.IsCylTest c (fun y => Φ s y i)) (x : ℝ × ℝ) :
    flatLap Φ s (x.1 + c, x.2) i = flatLap Φ s x i := by
  unfold flatLap
  exact lapP_periodic hψ x

lemma flatDt_periodic {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} {c : ℝ}
    (hper : ∀ s x i, Φ s (x.1 + c, x.2) i = Φ s x i) (s : ℝ) (x : ℝ × ℝ) (i : Fin 2) :
    flatDt Φ s (x.1 + c, x.2) i = flatDt Φ s x i := by
  unfold flatDt
  simp only [hper]

lemma pd_band_zero {R : ℝ} {φ : ℝ × ℝ → ℝ} (h : ∀ y : ℝ × ℝ, R < |y.2| → φ y = 0) (j : Fin 2)
    (x : ℝ × ℝ) (hx : R < |x.2|) : B0579.pd j φ x = 0 := by
  have hU : IsOpen {y : ℝ × ℝ | R < |y.2|} := isOpen_lt continuous_const continuous_snd.abs
  have hev : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => h y hy
  unfold B0579.pd
  rw [hev.fderiv_eq]
  simp

lemma flatLap_zero_band {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} {R s : ℝ} {i : Fin 2}
    (h : ∀ y : ℝ × ℝ, R < |y.2| → Φ s y i = 0) (x : ℝ × ℝ) (hx : R < |x.2|) :
    flatLap Φ s x i = 0 := by
  unfold flatLap lapP
  have h0 : ∀ y : ℝ × ℝ, R < |y.2| → B0579.pd 0 (fun z => Φ s z i) y = 0 :=
    fun y hy => pd_band_zero (φ := fun z => Φ s z i) h 0 y hy
  have h1 : ∀ y : ℝ × ℝ, R < |y.2| → B0579.pd 1 (fun z => Φ s z i) y = 0 :=
    fun y hy => pd_band_zero (φ := fun z => Φ s z i) h 1 y hy
  simp [pd_band_zero h0 0 x hx, pd_band_zero h1 1 x hx]

lemma pd_zero_fun (j : Fin 2) : B0579.pd j (fun _ : ℝ × ℝ => (0 : ℝ)) = fun _ => 0 := by
  funext x
  simp [B0579.pd]

lemma flatLap_zero_const {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} {s : ℝ} {i : Fin 2}
    (h : ∀ y : ℝ × ℝ, Φ s y i = 0) (x : ℝ × ℝ) : flatLap Φ s x i = 0 := by
  have e : (fun y => Φ s y i) = fun _ => (0 : ℝ) := funext fun y => h y
  unfold flatLap lapP
  rw [e]
  simp only [pd_zero_fun]
  simp [B0579.pd]

lemma flatDt_zero_gen {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} {s1 S2 R : ℝ}
    (hsupp : ∀ s x i, (s < s1 ∨ S2 < s ∨ R < |x.2|) → Φ s x i = 0)
    (s : ℝ) (x : ℝ × ℝ) (i : Fin 2) (h : s < s1 ∨ S2 < s ∨ R < |x.2|) :
    flatDt Φ s x i = 0 := by
  unfold flatDt
  rcases h with h | h | h
  · have hev : (fun s' => Φ s' x i) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with s' hs'
      exact hsupp s' x i (Or.inl hs')
    rw [hev.deriv_eq]
    simp
  · have hev : (fun s' => Φ s' x i) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h] with s' hs'
      exact hsupp s' x i (Or.inr (Or.inl hs'))
    rw [hev.deriv_eq]
    simp
  · have e : (fun s' => Φ s' x i) = fun _ => (0 : ℝ) :=
      funext fun s' => hsupp s' x i (Or.inr (Or.inr h))
    rw [e]
    simp

lemma psi1_zero {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} {s1 S2 R : ℝ} (ν : ℝ)
    (hsupp : ∀ s x i, (s < s1 ∨ S2 < s ∨ R < |x.2|) → Φ s x i = 0)
    (s : ℝ) (x : ℝ × ℝ) (i : Fin 2) (h : s < s1 ∨ S2 < s ∨ R < |x.2|) :
    psi1 ν Φ s x i = 0 := by
  have hD := flatDt_zero_gen hsupp s x i h
  have hL : flatLap Φ s x i = 0 := by
    rcases h with h | h | h
    · exact flatLap_zero_const (fun y => hsupp s y i (Or.inl h)) x
    · exact flatLap_zero_const (fun y => hsupp s y i (Or.inr (Or.inl h))) x
    · exact flatLap_zero_band (fun y hy => hsupp s y i (Or.inr (Or.inr hy))) x h
  unfold psi1
  rw [hD, hL]
  simp

lemma psi1_div {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : ∀ i, ContDiff ℝ ∞ (gI Φ i))
    (hdiv : ∀ s x, B0579.pd 0 (fun y => Φ s y 0) x + B0579.pd 1 (fun y => Φ s y 1) x = 0)
    (ν : ℝ) (s : ℝ) (x : ℝ × ℝ) :
    B0579.pd 0 (fun y => psi1 ν Φ s y 0) x + B0579.pd 1 (fun y => psi1 ν Φ s y 1) x = 0 := by
  have e0 : (fun y => psi1 ν Φ s y 0) = fun y => Psi3 ν Φ 0 (s, y) :=
    funext fun y => psi1_eq_fos hΦ ν s y 0
  have e1 : (fun y => psi1 ν Φ s y 1) = fun y => Psi3 ν Φ 1 (s, y) :=
    funext fun y => psi1_eq_fos hΦ ν s y 1
  have hC : ∀ q : V3, Dv eQ (gI Φ 0) q + Dv eH (gI Φ 1) q = 0 := by
    rintro ⟨q1, q2⟩
    have h' : B0579.pd 0 (fun y => gI Φ 0 (q1, y)) q2 +
        B0579.pd 1 (fun y => gI Φ 1 (q1, y)) q2 = 0 := hdiv q1 q2
    rw [pd_slice_Q (differentiable_fos (hΦ 0)) q1 q2,
      pd_slice_H (differentiable_fos (hΦ 1)) q1 q2] at h'
    exact h'
  rw [e0, e1, pd_slice_Q (differentiable_fos (psi3_contDiff hΦ ν 0)) s x,
    pd_slice_H (differentiable_fos (psi3_contDiff hΦ ν 1)) s x]
  exact alg_div_fos (gI Φ 0) (gI Φ 1) (hΦ 0) (hΦ 1) ν hC (s, x)

lemma isCylTest_slice {c : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ) (s : ℝ)
    (i : Fin 2) : B0579.IsCylTest c (fun y => Φ s y i) := by
  obtain ⟨s1, s2, R, _, hsupp⟩ := hΦ.support
  exact ⟨(hΦ.smooth i).comp ((contDiff_const (c := s)).prodMk contDiff_id),
    fun y => hΦ.periodic s y i, ⟨R, fun y hy => hsupp s y i (Or.inr (Or.inr hy))⟩⟩

lemma psi1_isDivFree {c : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ) (ν : ℝ)
    (s : ℝ) : IsDivFreeTestField c (fun x i => psi1 ν Φ s x i) := by
  obtain ⟨s1, s2, R, _, hsupp⟩ := hΦ.support
  have hG : ∀ i, ContDiff ℝ ∞ (gI Φ i) := fun i => hΦ.smooth i
  refine ⟨fun i => ⟨psi1_contDiff_x hG ν s i, ?_, ?_⟩, fun x => psi1_div hG hΦ.divFree ν s x⟩
  · intro x
    show psi1 ν Φ s (x.1 + c, x.2) i = psi1 ν Φ s x i
    unfold psi1
    rw [flatDt_periodic hΦ.periodic, flatLap_periodic s i (isCylTest_slice hΦ s i) x]
  · exact ⟨R, fun x hx => psi1_zero ν hsupp s x i (Or.inr (Or.inr hx))⟩

lemma psi2_isDivFree {c : ℝ} {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ) (s : ℝ) :
    IsDivFreeTestField c (fun x i => Φ s x i) :=
  ⟨fun i => isCylTest_slice hΦ s i, fun x => hΦ.divFree s x⟩

end UnforcedLeray.Short.IIIa.FOS
