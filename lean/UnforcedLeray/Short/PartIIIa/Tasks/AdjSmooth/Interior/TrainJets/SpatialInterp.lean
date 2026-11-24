import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.Interp1D
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.LineDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# `PartIII-a:T21/2/7/2/1/1/2/7`: weighted spatial interpolation of the train words

Proof of `TjSpatialInterp` (`Sub/AdjInterior/Train/Defs.lean`) by induction on the spatial word `L`
(`0 ∉ L`), with the weight `(1 + x₂²)^{γ'/2}` proved for all `0 ≤ γ' < β` at once. A letter
`a ≠ 0` is peeled off the front: along the line through `(ρ, x)` in direction `stDir a` the function
`tjW L' h` has derivatives `tjW (replicate N a ++ L') h`, bounded by hypothesis, and the induction
hypothesis at the weight `s = (γ' + β)/2` bounds the function itself (up to a factor `(1 + x₂²)^{-s/2}`,
since `1 + x₂² ≤ 3 (1 + y₂²)` on a unit segment). `Interp1D` with `N` so large that `s(1 - 1/N) ≥ γ'`
then gives the bound of `tjW (a :: L') h` with weight `γ'`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The spatial directions `stDir b`, `b ≠ 0`, leave the age fixed and have a unit-bounded `η`
component. -/
theorem tjStDir_spatial (b : Fin 3) (hb : b ≠ 0) :
    (stDir b).1 = 0 ∧ |(stDir b).2.2| ≤ 1 := by
  fin_cases b <;> simp_all [stDir]

theorem tjSpatialInterp : TjSpatialInterp := by
  intro β γ hγ0 hγβ h hh S hS hAb hMb
  have main : ∀ L : List (Fin 3), 0 ∉ L → ∀ γ' : ℝ, 0 ≤ γ' → γ' < β →
      ∃ C : ℝ, ∀ ρ ∈ Icc (0 : ℝ) S, ∀ x : ℝ × ℝ,
        (1 + x.2 ^ 2) ^ (γ' / 2) * |tjW L h (ρ, x)| ≤ C := by
    intro L
    induction L with
    | nil =>
      intro _ γ' hγ'0 hγ'β
      obtain ⟨A, hA⟩ := hAb
      refine ⟨A, fun ρ hρ x => ?_⟩
      have hle : (1 + x.2 ^ 2) ^ (γ' / 2) ≤ (1 + x.2 ^ 2) ^ (β / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg x.2]) (by linarith)
      calc (1 + x.2 ^ 2) ^ (γ' / 2) * |tjW [] h (ρ, x)|
          = (1 + x.2 ^ 2) ^ (γ' / 2) * |h (ρ, x)| := rfl
        _ ≤ (1 + x.2 ^ 2) ^ (β / 2) * |h (ρ, x)| :=
          mul_le_mul_of_nonneg_right hle (abs_nonneg _)
        _ ≤ A := hA ρ hρ x
    | cons a L' ih =>
      intro hL γ' hγ'0 hγ'β
      have ha : a ≠ 0 := fun h' => hL (by simp [h'])
      have hL' : (0 : Fin 3) ∉ L' := fun h' => hL (List.mem_cons_of_mem _ h')
      obtain ⟨hs1, hs2⟩ := tjStDir_spatial a ha
      obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (γ' + β) / 2 := ⟨_, rfl⟩
      have hspos : 0 < s := by rw [hs]; linarith
      have hγs : γ' < s := by rw [hs]; linarith
      have hsβ : s < β := by rw [hs]; linarith
      obtain ⟨C'', hC''⟩ := ih hL' s hspos.le hsβ
      have hC0 : 0 ≤ C'' :=
        le_trans (mul_nonneg (Real.rpow_nonneg (by positivity) _) (abs_nonneg _))
          (hC'' 0 ⟨le_refl _, hS⟩ 0)
      obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (3 : ℝ) ^ (s / 2) * C'' := ⟨_, rfl⟩
      have hc0 : 0 ≤ c := by
        rw [hc]; exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) hC0
      obtain ⟨N, hN⟩ := exists_nat_gt (s / (s - γ'))
      have hsg : 0 < s - γ' := by linarith
      have hN0 : (0 : ℝ) < N := lt_trans (div_pos hspos hsg) hN
      have hN1 : 1 ≤ N := by
        have : (0 : ℕ) < N := by exact_mod_cast hN0
        omega
      have h2 : s < N * (s - γ') := (div_lt_iff₀ hsg).1 hN
      obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 1 - 1 / (N : ℝ) := ⟨_, rfl⟩
      have hkey : γ' ≤ s * θ := by
        have h3 : s / (N : ℝ) ≤ s - γ' := by
          rw [div_le_iff₀ hN0]; nlinarith [h2]
        have h4 : s * θ = s - s / (N : ℝ) := by rw [hθ]; ring
        linarith
      have hL0 : (0 : Fin 3) ∉ List.replicate N a ++ L' := by
        intro hmem
        rcases List.mem_append.1 hmem with h1 | h1
        · exact ha (List.eq_of_mem_replicate h1).symm
        · exact hL' h1
      obtain ⟨M, hM⟩ := hMb (List.replicate N a ++ L') hL0
      have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 ⟨le_refl _, hS⟩ 0)
      obtain ⟨K, hK0, hK⟩ := interp1D N hN1
      obtain ⟨Mr, hMr⟩ : ∃ Mr : ℝ, Mr = M ^ (1 / (N : ℝ)) := ⟨_, rfl⟩
      have hMr0 : 0 ≤ Mr := by rw [hMr]; exact Real.rpow_nonneg hM0 _
      refine ⟨K * (c ^ θ * Mr + c), fun ρ hρ x => ?_⟩
      have hρ0 : 0 ≤ ρ := hρ.1
      have hp : ((ρ, x) : ℝ × (ℝ × ℝ)) ∈ tjU := ⟨mem_Ici.2 hρ0, mem_univ _⟩
      have hWC : ContDiffOn ℝ ∞ (tjW L' h) tjU := tjW_contDiffOn hh L'
      obtain ⟨hgC, hgD⟩ := tjLineDeriv (tjW L' h) hWC a ha (ρ, x) hp
      have hgCN : ContDiff ℝ N (fun t : ℝ => tjW L' h ((ρ, x) + t • stDir a)) :=
        hgC.of_le (by exact_mod_cast le_top)
      have hq1gen : ∀ t : ℝ, ((ρ, x) + t • stDir a).1 = ρ := fun t => by simp [hs1]
      have hderiv0 : deriv (fun t : ℝ => tjW L' h ((ρ, x) + t • stDir a)) 0
          = tjW (a :: L') h (ρ, x) := by
        have e1 := hgD 1 0
        rw [iteratedDeriv_one, zero_smul, add_zero] at e1
        rw [e1, ← tjW_append]
        rfl
      have hgM : ∀ t ∈ Icc (0 : ℝ) (0 + 1),
          |iteratedDeriv N (fun t : ℝ => tjW L' h ((ρ, x) + t • stDir a)) t| ≤ M := by
        intro t _
        rw [hgD N t, ← tjW_append]
        exact hM (((ρ, x) + t • stDir a).1) (by rw [hq1gen t]; exact hρ)
          (((ρ, x) + t • stDir a).2)
      have hpt : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          |tjW L' h ((ρ, x) + t • stDir a)| ≤ c * (1 + x.2 ^ 2) ^ (-(s / 2)) := by
        intro t ht0 ht1
        have hq2 : |((ρ, x) + t • stDir a).2.2 - x.2| ≤ 1 := by
          have e : ((ρ, x) + t • stDir a).2.2 - x.2 = t * (stDir a).2.2 := by
            simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; ring
          rw [e, abs_mul, abs_of_nonneg ht0]
          nlinarith [abs_nonneg (stDir a).2.2]
        obtain ⟨q, hqdef⟩ : ∃ q : ℝ × (ℝ × ℝ), q = (ρ, x) + t • stDir a := ⟨_, rfl⟩
        rw [← hqdef] at hq2 ⊢
        have hq1 : q.1 = ρ := by rw [hqdef]; exact hq1gen t
        have hd := abs_le.1 hq2
        have hd2 : (q.2.2 - x.2) ^ 2 ≤ 1 := by nlinarith [hd.1, hd.2]
        have hP0 : (0 : ℝ) < 1 + x.2 ^ 2 := by positivity
        have hQ0 : (0 : ℝ) < 1 + q.2.2 ^ 2 := by positivity
        have hPQ : 1 + x.2 ^ 2 ≤ 3 * (1 + q.2.2 ^ 2) := by
          nlinarith [sq_nonneg (2 * q.2.2 - x.2), sq_nonneg q.2.2, hd2]
        have hIH := hC'' q.1 (by rw [hq1]; exact hρ) q.2
        rw [Prod.mk.eta] at hIH
        have hPs : (1 + x.2 ^ 2) ^ (s / 2) ≤ (3 : ℝ) ^ (s / 2) * (1 + q.2.2 ^ 2) ^ (s / 2) := by
          calc (1 + x.2 ^ 2) ^ (s / 2) ≤ (3 * (1 + q.2.2 ^ 2)) ^ (s / 2) :=
                Real.rpow_le_rpow hP0.le hPQ (by linarith)
            _ = (3 : ℝ) ^ (s / 2) * (1 + q.2.2 ^ 2) ^ (s / 2) :=
                Real.mul_rpow (by norm_num) hQ0.le
        have hPs0 : 0 < (1 + x.2 ^ 2) ^ (s / 2) := Real.rpow_pos_of_pos hP0 _
        have hmain : |tjW L' h q| * (1 + x.2 ^ 2) ^ (s / 2) ≤ c := by
          calc |tjW L' h q| * (1 + x.2 ^ 2) ^ (s / 2)
              ≤ |tjW L' h q| * ((3 : ℝ) ^ (s / 2) * (1 + q.2.2 ^ 2) ^ (s / 2)) :=
                mul_le_mul_of_nonneg_left hPs (abs_nonneg _)
            _ = (3 : ℝ) ^ (s / 2) * ((1 + q.2.2 ^ 2) ^ (s / 2) * |tjW L' h q|) := by ring
            _ ≤ (3 : ℝ) ^ (s / 2) * C'' :=
                mul_le_mul_of_nonneg_left hIH (Real.rpow_nonneg (by norm_num) _)
            _ = c := by rw [hc]
        rw [Real.rpow_neg hP0.le]
        calc |tjW L' h q| = |tjW L' h q| * (1 + x.2 ^ 2) ^ (s / 2)
              * ((1 + x.2 ^ 2) ^ (s / 2))⁻¹ :=
              (mul_inv_cancel_right₀ hPs0.ne' _).symm
          _ ≤ c * ((1 + x.2 ^ 2) ^ (s / 2))⁻¹ :=
              mul_le_mul_of_nonneg_right hmain (inv_nonneg.2 hPs0.le)
      have hgA : ∀ t ∈ Icc (0 : ℝ) (0 + 1),
          |(fun t : ℝ => tjW L' h ((ρ, x) + t • stDir a)) t| ≤ c * (1 + x.2 ^ 2) ^ (-(s / 2)) :=
        fun t ht => hpt t ht.1 (by linarith [ht.2])
      have hKapp := hK (fun t : ℝ => tjW L' h ((ρ, x) + t • stDir a)) 0
        (c * (1 + x.2 ^ 2) ^ (-(s / 2))) M hgCN hgA hgM
      rw [hderiv0, ← hθ, ← hMr] at hKapp
      have hP1 : (1 : ℝ) ≤ 1 + x.2 ^ 2 := by nlinarith [sq_nonneg x.2]
      have hP0 : (0 : ℝ) < 1 + x.2 ^ 2 := by linarith
      have hu0 : 0 ≤ (1 + x.2 ^ 2) ^ (γ' / 2) := Real.rpow_nonneg hP0.le _
      have hR0 : 0 ≤ (1 + x.2 ^ 2) ^ (-(s / 2)) := Real.rpow_nonneg hP0.le _
      have hA1 : (1 + x.2 ^ 2) ^ (γ' / 2) * (c * (1 + x.2 ^ 2) ^ (-(s / 2))) ^ θ
          ≤ c ^ θ := by
        have e1 : (c * (1 + x.2 ^ 2) ^ (-(s / 2))) ^ θ = c ^ θ * (1 + x.2 ^ 2) ^ (-(s / 2) * θ) := by
          rw [Real.mul_rpow hc0 hR0, ← Real.rpow_mul hP0.le]
        have e2 : (1 + x.2 ^ 2) ^ (γ' / 2) * (1 + x.2 ^ 2) ^ (-(s / 2) * θ)
            = (1 + x.2 ^ 2) ^ (γ' / 2 + -(s / 2) * θ) := (Real.rpow_add hP0 _ _).symm
        have le2 : (1 + x.2 ^ 2) ^ (γ' / 2 + -(s / 2) * θ) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hP1 (by linarith [hkey])
        calc (1 + x.2 ^ 2) ^ (γ' / 2) * (c * (1 + x.2 ^ 2) ^ (-(s / 2))) ^ θ
            = c ^ θ * ((1 + x.2 ^ 2) ^ (γ' / 2) * (1 + x.2 ^ 2) ^ (-(s / 2) * θ)) := by
              rw [e1]; ring
          _ = c ^ θ * (1 + x.2 ^ 2) ^ (γ' / 2 + -(s / 2) * θ) := by rw [e2]
          _ ≤ c ^ θ * 1 := mul_le_mul_of_nonneg_left le2 (Real.rpow_nonneg hc0 _)
          _ = c ^ θ := mul_one _
      have hA2 : (1 + x.2 ^ 2) ^ (γ' / 2) * (c * (1 + x.2 ^ 2) ^ (-(s / 2))) ≤ c := by
        have e2 : (1 + x.2 ^ 2) ^ (γ' / 2) * (1 + x.2 ^ 2) ^ (-(s / 2))
            = (1 + x.2 ^ 2) ^ (γ' / 2 + -(s / 2)) := (Real.rpow_add hP0 _ _).symm
        have le1 : (1 + x.2 ^ 2) ^ (γ' / 2 + -(s / 2)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hP1 (by linarith)
        calc (1 + x.2 ^ 2) ^ (γ' / 2) * (c * (1 + x.2 ^ 2) ^ (-(s / 2)))
            = c * ((1 + x.2 ^ 2) ^ (γ' / 2) * (1 + x.2 ^ 2) ^ (-(s / 2))) := by ring
          _ = c * (1 + x.2 ^ 2) ^ (γ' / 2 + -(s / 2)) := by rw [e2]
          _ ≤ c * 1 := mul_le_mul_of_nonneg_left le1 hc0
          _ = c := mul_one c
      calc (1 + x.2 ^ 2) ^ (γ' / 2) * |tjW (a :: L') h (ρ, x)|
          ≤ (1 + x.2 ^ 2) ^ (γ' / 2) *
              (K * ((c * (1 + x.2 ^ 2) ^ (-(s / 2))) ^ θ * Mr
                + c * (1 + x.2 ^ 2) ^ (-(s / 2)))) :=
            mul_le_mul_of_nonneg_left hKapp hu0
        _ = K * (((1 + x.2 ^ 2) ^ (γ' / 2) * (c * (1 + x.2 ^ 2) ^ (-(s / 2))) ^ θ) * Mr
                + (1 + x.2 ^ 2) ^ (γ' / 2) * (c * (1 + x.2 ^ 2) ^ (-(s / 2)))) := by ring
        _ ≤ K * (c ^ θ * Mr + c) := by
          refine mul_le_mul_of_nonneg_left ?_ hK0
          have := mul_le_mul_of_nonneg_right hA1 hMr0
          linarith [hA2]
  intro L hL
  exact main L hL γ hγ0 hγβ

end UnforcedLeray.Short.IIIa
