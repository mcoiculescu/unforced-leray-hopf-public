import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSobolev.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.SliceAe.PeriodicBoxBound

/-!
# `PartIII-a:T21/2/7/2/1/1/7/5`: unfolding the plane integral onto the cell

Source: `the November 2 reference manuscript` lines 3060-3061.
For `c`-periodic locally integrable `h` and `θ ∈ C_c^∞(ℝ²)`, `∫_{ℝ²} h θ = ∫_cell h (perTest c θ)`.
The plane is cut into the translates `cell + (kc, 0)` (`cl k`), only finitely many of which meet
`tsupport θ`; each piece is moved back to the cell by periodicity of `h` (`pb_shift_eq`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem perTestUnfold : UnforcedLeray.Short.IIIa.PerTestUnfold := by
  intro c θ h hc hθ hθc hper hLI
  have hK : IsCompact (tsupport θ) := hθc.isCompact
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (continuous_fst.continuousOn)
  have memcell : ∀ x : ℝ × ℝ, x ∈ B0579.cell c ↔ -(c / 2) ≤ x.1 ∧ x.1 < c / 2 := by
    intro x
    simp [B0579.cell, Set.mem_prod, Set.mem_Ico]
  -- the translates `cell + (kc, 0)`
  obtain ⟨cl, hcl⟩ : ∃ cl : ℤ → Set (ℝ × ℝ),
      cl = fun k : ℤ => (fun x : ℝ × ℝ => x - ((k : ℝ) * c, (0 : ℝ))) ⁻¹' B0579.cell c := ⟨_, rfl⟩
  have memcl : ∀ (k : ℤ) (x : ℝ × ℝ), x ∈ cl k ↔
      -(c / 2) ≤ x.1 - (k : ℝ) * c ∧ x.1 - (k : ℝ) * c < c / 2 := by
    intro k x
    simp [hcl, memcell]
  have meascl : ∀ k : ℤ, MeasurableSet (cl k) := fun k => by
    rw [hcl]
    exact (B0579.measurableSet_cell c).preimage (measurable_id.sub_const _)
  have disj : ∀ j k : ℤ, j ≠ k → Disjoint (cl j) (cl k) := by
    intro j k hjk
    rw [Set.disjoint_left]
    intro x hxj hxk
    rw [memcl] at hxj hxk
    have e1 : ((k : ℝ) - j) * c = (x.1 - (j : ℝ) * c) - (x.1 - (k : ℝ) * c) := by ring
    have h1 : ((k : ℝ) - j) * c < c := by linarith [hxj.1, hxj.2, hxk.1, hxk.2]
    have h2 : -c < ((k : ℝ) - j) * c := by linarith [hxj.1, hxj.2, hxk.1, hxk.2]
    have h1' : (k : ℝ) - j < 1 := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    have h2' : -1 < (k : ℝ) - j := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    have h3 : k - j < 1 := by exact_mod_cast h1'
    have h4 : -1 < k - j := by exact_mod_cast h2'
    exact hjk (by omega)
  -- a finite range of indices `[-M, M]` covering the bounded support
  obtain ⟨M, hM⟩ : ∃ M : ℤ, A + c ≤ (M : ℝ) * c :=
    ⟨⌈(A + c) / c⌉, (div_le_iff₀ hc).1 (Int.le_ceil _)⟩
  have cover : ∀ x : ℝ × ℝ, |x.1| ≤ A → ∃ k : ℤ, -M ≤ k ∧ k ≤ M ∧ x ∈ cl k := by
    intro x hx
    obtain ⟨k, hk⟩ : ∃ k : ℤ, k = ⌊(x.1 + c / 2) / c⌋ := ⟨_, rfl⟩
    have hf1 : (k : ℝ) ≤ (x.1 + c / 2) / c := by
      rw [hk]
      exact Int.floor_le _
    have hf2 : (x.1 + c / 2) / c < (k : ℝ) + 1 := by
      rw [hk]
      exact Int.lt_floor_add_one _
    have hf1' : (k : ℝ) * c ≤ x.1 + c / 2 := (le_div_iff₀ hc).1 hf1
    have hf2' : x.1 + c / 2 < ((k : ℝ) + 1) * c := (div_lt_iff₀ hc).1 hf2
    have hx' := abs_le.1 hx
    refine ⟨k, ?_, ?_, ?_⟩
    · have h3 : -(M : ℝ) < (k : ℝ) + 1 := lt_of_mul_lt_mul_right (by nlinarith) hc.le
      have h4 : (-M - 1 : ℤ) < k := by
        have : ((-M - 1 : ℤ) : ℝ) < (k : ℝ) := by
          push_cast
          linarith
        exact_mod_cast this
      omega
    · have h3 : (k : ℝ) ≤ (M : ℝ) := le_of_mul_le_mul_right (by nlinarith) hc
      exact_mod_cast h3
    · rw [memcl]
      constructor <;> linarith
  -- the periodization is a finite sum on the cell
  have hpt : ∀ (g : ℝ × ℝ → ℝ) (x : ℝ × ℝ),
      perTest c g x = ∑ᶠ k : ℤ, g (x + ((k : ℝ) * c, (0 : ℝ))) := by
    intro g x
    unfold perTest
    apply finsum_congr
    intro k
    congr 1
    ext <;> simp
  have hsupp : ∀ y ∈ B0579.cell c,
      perTest c θ y = ∑ k ∈ Finset.Icc (-M) M, θ (y + ((k : ℝ) * c, (0 : ℝ))) := by
    intro y hy
    rw [memcell] at hy
    rw [hpt]
    apply finsum_eq_sum_of_support_subset
    intro k hk
    have hne : θ (y + ((k : ℝ) * c, (0 : ℝ))) ≠ 0 := Function.mem_support.1 hk
    have hmem : y + ((k : ℝ) * c, (0 : ℝ)) ∈ tsupport θ :=
      subset_tsupport _ (Function.mem_support.2 hne)
    have hb : |y.1 + (k : ℝ) * c| ≤ A := by
      have := hA _ hmem
      simpa [Real.norm_eq_abs] using this
    have h1 := abs_le.1 hb
    have hkc1 : (k : ℝ) * c ≤ (M : ℝ) * c := by linarith [h1.2, hy.1, hM, hc]
    have hkc2 : -(k : ℝ) * c ≤ (M : ℝ) * c := by linarith [h1.1, hy.2, hM, hc]
    have hk1 : (k : ℝ) ≤ (M : ℝ) := le_of_mul_le_mul_right hkc1 hc
    have hk2 : -(k : ℝ) ≤ (M : ℝ) := le_of_mul_le_mul_right hkc2 hc
    have hk1' : k ≤ M := by exact_mod_cast hk1
    have hk2' : -k ≤ M := by exact_mod_cast hk2
    exact Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨by omega, hk1'⟩)
  -- periodicity of `h` in the first variable
  have hshift : ∀ (k : ℤ) (y : ℝ × ℝ), h (y + ((k : ℝ) * c, (0 : ℝ))) = h y := by
    intro k y
    have e : y + ((k : ℝ) * c, (0 : ℝ)) = y - (((-k : ℤ) : ℝ) * c, (0 : ℝ)) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
        Prod.fst_zero, Prod.snd_zero, Int.cast_neg] <;> ring
    rw [e]
    exact pb_shift_eq hper (-k) y
  -- integration over a translate of the cell
  have hemb : ∀ k : ℤ, MeasurableEmbedding (fun x : ℝ × ℝ => x - ((k : ℝ) * c, (0 : ℝ))) :=
    fun k => measurableEmbedding_subRight _
  have hTrans : ∀ (G : ℝ × ℝ → ℂ) (k : ℤ),
      ∫ x in cl k, G x = ∫ y in B0579.cell c, G (y + ((k : ℝ) * c, (0 : ℝ))) := by
    intro G k
    have e := (measurePreserving_sub_right volume ((k : ℝ) * c, (0 : ℝ))).setIntegral_preimage_emb
      (hemb k) (fun y => G (y + ((k : ℝ) * c, (0 : ℝ)))) (B0579.cell c)
    rw [hcl]
    simpa only [sub_add_cancel] using e
  have transInt : ∀ (G : ℝ × ℝ → ℂ), Integrable G → ∀ k : ℤ,
      IntegrableOn (fun y => G (y + ((k : ℝ) * c, (0 : ℝ)))) (B0579.cell c) := by
    intro G hG k
    have hmp := measurePreserving_add_right volume ((k : ℝ) * c, (0 : ℝ))
    have hem : MeasurableEmbedding (fun x : ℝ × ℝ => x + ((k : ℝ) * c, (0 : ℝ))) :=
      measurableEmbedding_addRight _
    exact ((hmp.integrable_comp_emb hem).2 hG).integrableOn
  -- integrability of `h θ`
  have hg : Integrable (fun x => h x * (θ x : ℂ)) := by
    refine (LocallyIntegrable.integrable_smul_left_of_hasCompactSupport (𝕜 := ℝ) hLI
      hθ.continuous hθc).congr (Filter.Eventually.of_forall fun x => ?_)
    show θ x • h x = h x * (θ x : ℂ)
    rw [Complex.real_smul, mul_comm]
  -- the integral over `ℝ²` is the sum of the integrals over the translates
  have hzero : ∀ x : ℝ × ℝ, x ∉ ⋃ k ∈ Finset.Icc (-M) M, cl k → h x * (θ x : ℂ) = 0 := by
    intro x hx
    by_cases hθx : θ x = 0
    · simp [hθx]
    · exfalso
      have hmem : x ∈ tsupport θ := subset_tsupport _ (Function.mem_support.2 hθx)
      have hb : |x.1| ≤ A := by
        have := hA x hmem
        rwa [Real.norm_eq_abs] at this
      obtain ⟨k, hk1, hk2, hxk⟩ := cover x hb
      exact hx (Set.mem_iUnion₂.2 ⟨k, Finset.mem_Icc.2 ⟨hk1, hk2⟩, hxk⟩)
  have hU := integral_biUnion_finset (Finset.Icc (-M) M) (fun k _ => meascl k)
    (fun j _ k _ hjk => disj j k hjk) (fun k _ => hg.integrableOn)
  have hF_int : ∫ x, h x * (θ x : ℂ) = ∑ k ∈ Finset.Icc (-M) M, ∫ x in cl k, h x * (θ x : ℂ) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm.trans hU
  -- on the cell the finite sum is the periodization
  have hsum : ∀ y ∈ B0579.cell c,
      ∑ k ∈ Finset.Icc (-M) M, h (y + ((k : ℝ) * c, (0 : ℝ))) * (θ (y + ((k : ℝ) * c, (0 : ℝ))) : ℂ)
        = h y * (perTest c θ y : ℂ) := by
    intro y hy
    rw [hsupp y hy, Complex.ofReal_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [hshift k y]
  have hF : ∫ x, h x * (θ x : ℂ) = ∫ y in B0579.cell c, h y * (perTest c θ y : ℂ) := by
    have step1 : ∑ k ∈ Finset.Icc (-M) M, ∫ x in cl k, h x * (θ x : ℂ) =
        ∑ k ∈ Finset.Icc (-M) M, ∫ y in B0579.cell c,
          h (y + ((k : ℝ) * c, (0 : ℝ))) * (θ (y + ((k : ℝ) * c, (0 : ℝ))) : ℂ) :=
      Finset.sum_congr rfl fun k _ => hTrans _ k
    rw [hF_int, step1, ← integral_finsetSum _ (fun k _ => transInt _ hg k)]
    apply setIntegral_congr_fun (B0579.measurableSet_cell c)
    intro y hy
    exact hsum y hy
  have hIntP : IntegrableOn (fun x => h x * (perTest c θ x : ℂ)) (B0579.cell c) := by
    have hsumI : IntegrableOn
        (fun y => ∑ k ∈ Finset.Icc (-M) M,
          h (y + ((k : ℝ) * c, (0 : ℝ))) * (θ (y + ((k : ℝ) * c, (0 : ℝ))) : ℂ))
        (B0579.cell c) :=
      integrable_finsetSum _ (fun k _ => transInt _ hg k)
    exact hsumI.congr_fun (fun y hy => hsum y hy) (B0579.measurableSet_cell c)
  exact ⟨hg, hIntP, hF⟩

end UnforcedLeray.Short.IIIa
