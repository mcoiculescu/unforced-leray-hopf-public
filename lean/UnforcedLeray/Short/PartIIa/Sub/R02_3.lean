import UnforcedLeray.Short.PartIIa.Sub.R02_2

/-!
# Part II-a, task `PartII-a:R02/3`: the mean-remainder profile bounds (decomposition, conditional)

Source of record: `the November 2 reference manuscript`, lines 447-459
(`sct:expansion`) and 1259-1276 (late residual table).

Target: `LateMeanRemainder` (`Sub/R02.lean`): for the remainder `R_N = S - ∑_{j≤N} a_{2j} ∂_η^{2j}
G_{νs}` of the mean stream, `(1+η²/s)^m |K^ℓ ∂_η^b R_N| ≤ P s^{-(b+2N+3)/2}` for `s ≥ 1`.


`Sub/R02_2.lean`, which this file imports):

* shared with `R02/2`: `KExpansion`, `ProfileIterComm`, `ProfileDict` (profile partials are nested
  `iteratedDeriv`s; with `b = 0` this is the `∂_η^j ∂_s^k` dictionary of the route);
* new leaves: `HeatKernelIterSmooth`, `MeanRemainderSmooth` (joint smoothness of `R_N` for `s > 0`,
  from `TrainMeanEquations` and the heat kernel), `SliceDerivContinuous`, `EssSupPointwise`
  (a continuous function's pointwise value is bounded by its `L^∞` norm), and `MeanRemPointwise`
  (the `p = ∞` case of `TrainMeanExpansion` read pointwise);
* proved here: `meanRemTerm_of` (the weight `(1+η²/s)^m ≤ 2^m (1 + (η²/s)^m)` is split into two
  `TrainMeanExpansion` bounds, at `m' = i` and `m' = 2m+i`, and the powers of `s` are collected)
  and `lateMeanRemainder_of_sub`, the conditional theorem, via the finite assembly
  `late_assembly` of `Sub/R02_2.lean` (with the `κ`-independent decay `s^{-(b+2N+3)/2}`).

The unconditional statement `lateMeanRemainder_of (hM) (hE) (hS) : LateMeanRemainder` is the task
file `Short/PartII-a/Tasks/R02/MeanRemainder.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (meanStream meanRemainder heatKernel1)

/-! ### Leaves -/

/-- **Joint smoothness of the heat kernel's `η`-derivatives** (elementary): for `ν > 0` and
`k : ℕ`, `(s, η) ↦ ∂_η^k G_{νs}(η)` is `C^∞` on `(0, ∞) × ℝ`, where
`G_t(η) = (4πt)^{-1/2} e^{-η²/(4t)}` (`heatKernel1`).  (`G` is `C^∞` on `(0,∞) × ℝ`; the
`η`-derivative of a jointly `C^∞` function is jointly `C^∞`:
`iteratedDeriv k (fun e => f (s, e)) η = iteratedFDeriv ℝ k f (s, η) (fun _ => (0,1))`.) -/
def HeatKernelIterSmooth : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ k : ℕ,
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => iteratedDeriv k (fun e => heatKernel1 (ν * x.1) e) x.2)
      (Ioi 0 ×ˢ univ)

/-- **Joint smoothness of the mean remainder** (`sct:mean`, `sct:expansion`; source lines
397-404, 447-449): `R_N(s, η) = S(s, η) - ∑_{j≤N} a_{2j} ∂_η^{2j} G_{νs}(η)` is `C^∞` on
`(0,∞) × ℝ`.  (`S` is by `TrainMeanEquations.1`, the finite sum by `HeatKernelIterSmooth`.) -/
def MeanRemainderSmooth : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ N : ℕ,
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) (Ioi 0 ×ˢ univ)

/-- **Continuity of the slice derivatives** (calculus): if `G` is jointly `C^∞` on
`(0,∞) × ℝ`, then for each age `s > 0`, `η ↦ ∂_η^b ∂_s^ℓ G(s, η)` is continuous.  (The age
derivative `(s, η) ↦ iteratedDeriv ℓ (fun r => G r η) s` is again jointly `C^∞` on the open set;
restrict to the slice `s` and differentiate `b` times in `η`.) -/
def SliceDerivContinuous : Prop :=
  ∀ G : ℝ → ℝ → ℝ, ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => G x.1 x.2) (Ioi 0 ×ˢ univ) →
    ∀ (b ℓ : ℕ) (s : ℝ), 0 < s →
      Continuous (fun η => iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => G r e) s) η)

/-- **A continuous function is bounded pointwise by its essential supremum** (measure theory):
`‖f‖_{L^∞(ℝ)} ≤ B` and `f` continuous give `|f x| ≤ B` for every `x`.  (`ae_le_eLpNormEssSup`;
the set `{x | |f x| ≤ B}` is closed and of full measure, hence everything since `volume` charges
open sets.) -/
def EssSupPointwise : Prop :=
  ∀ f : ℝ → ℝ, Continuous f → ∀ B : ℝ, 0 ≤ B →
    eLpNorm f ⊤ volume ≤ ENNReal.ofReal B → ∀ x : ℝ, |f x| ≤ B

/-- **`TrainMeanExpansion` at `p = ∞`, read pointwise** (source lines 447-459): for fixed
`ρ, N, m', b', ℓ'` there are a polynomial majorant `C(1+c+ν⁻¹)^M` and `ν₀ > 0` with
`|η|^{m'} |∂_η^{b'} ∂_s^{ℓ'} R_N(s, η)| ≤ P s^{(m'-b'-2N-3)/2-ℓ'}` for all `s ≥ 1`, `η ∈ ℝ`.
(From the `p = ⊤` case of `TrainMeanExpansion`, where `ENNReal.toReal ⊤ = 0` removes the term
`1/(2p)`; the function `η ↦ η^{m'} ∂_η^{b'} ∂_s^{ℓ'} R_N(s, η)` is continuous by
`MeanRemainderSmooth` and `SliceDerivContinuous`, so `EssSupPointwise` applies.) -/
def MeanRemPointwise : Prop :=
  ∀ (ρ : ℝ) (N m' b' l' : ℕ), 1 / 2 < ρ → ∃ (C : ℝ) (M : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ s : ℝ, 1 ≤ s → ∀ η : ℝ,
        |η| ^ m' * |iteratedDeriv b' (fun e => iteratedDeriv l'
            (fun r => meanRemainder tr N r e) s) η| ≤
          polyConst C M ν (ν ^ (-ρ)) * s ^ (((m' : ℝ) - b' - 2 * N - 3) / 2 - l')

/-! ### The term bound (proved) -/

theorem pow_one_add_le (m : ℕ) {t : ℝ} (ht : 0 ≤ t) : (1 + t) ^ m ≤ 2 ^ m * (1 + t ^ m) := by
  rcases le_total t 1 with h | h
  · calc (1 + t) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ ≤ 2 ^ m * (1 + t ^ m) :=
        le_mul_of_one_le_right (by positivity) (by have := pow_nonneg ht m; linarith)
  · calc (1 + t) ^ m ≤ (2 * t) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ = 2 ^ m * t ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (1 + t ^ m) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- The term bound at the level of `(s, η)`: the weight `(1+η²/s)^m` is split into
`2^m (1 + (η²/s)^m)` and the two pieces are bounded by `MeanRemPointwise` at `m' = i` and
`m' = 2m+i` (both with `b' = i+b`, `ℓ' = k`). -/
theorem meanRemTerm_of (hPt : MeanRemPointwise) (ρ : ℝ) (N m b i k : ℕ) (hρ : 1 / 2 < ρ) :
    ∃ (C : ℝ) (M : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ s η : ℝ, 1 ≤ s →
          (1 + η ^ 2 / s) ^ m * (|η| ^ i * s ^ k *
            |iteratedDeriv (i + b) (fun e => iteratedDeriv k
              (fun r => meanRemainder tr N r e) s) η|) ≤
            polyConst C M ν (ν ^ (-ρ)) * s ^ (-(((b : ℝ) + 2 * N + 3) / 2)) := by
  obtain ⟨CA, MA, νA, hνA, HA⟩ := hPt ρ N i (i + b) k hρ
  obtain ⟨CB, MB, νB, hνB, HB⟩ := hPt ρ N (2 * m + i) (i + b) k hρ
  refine ⟨2 ^ m * (max CA 0 + max CB 0), MA + MB, min νA νB, lt_min hνA hνB, ?_⟩
  intro ν hν hνle tr hb s η hs
  have hs0 : 0 < s := by linarith
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
  set d := |iteratedDeriv (i + b) (fun e => iteratedDeriv k
    (fun r => meanRemainder tr N r e) s) η| with hd
  have hd0 : 0 ≤ d := abs_nonneg _
  set β : ℝ := ((b : ℝ) + 2 * N + 3) / 2 with hβ
  have hA := HA ν hν (hνle.trans (min_le_left _ _)) tr hb s hs η
  have hB := HB ν hν (hνle.trans (min_le_right _ _)) tr hb s hs η
  have eA : (((i : ℕ) : ℝ) - ((i + b : ℕ) : ℝ) - 2 * N - 3) / 2 - k = -β - k := by
    rw [hβ]; push_cast; ring
  have eB : (((2 * m + i : ℕ) : ℝ) - ((i + b : ℕ) : ℝ) - 2 * N - 3) / 2 - k = m - β - k := by
    rw [hβ]; push_cast; ring
  rw [eA] at hA
  rw [eB] at hB
  set PA := polyConst CA MA ν (ν ^ (-ρ)) with hPA
  set PB := polyConst CB MB ν (ν ^ (-ρ)) with hPB
  have hsk : (0 : ℝ) ≤ s ^ k := by positivity
  -- the first piece
  have k1 : s ^ k * (|η| ^ i * d) ≤ PA * s ^ (-β) := by
    calc s ^ k * (|η| ^ i * d) ≤ s ^ k * (PA * s ^ (-β - (k : ℝ))) :=
          mul_le_mul_of_nonneg_left hA hsk
      _ = PA * s ^ (-β) := by
          rw [← Real.rpow_natCast s k]
          have : s ^ (k : ℝ) * s ^ (-β - (k : ℝ)) = s ^ (-β) := by
            rw [← Real.rpow_add hs0]; congr 1; ring
          calc s ^ (k : ℝ) * (PA * s ^ (-β - (k : ℝ)))
              = PA * (s ^ (k : ℝ) * s ^ (-β - (k : ℝ))) := by ring
            _ = PA * s ^ (-β) := by rw [this]
  -- the second piece
  have k2 : s ^ k * ((η ^ 2 / s) ^ m * (|η| ^ i * d)) ≤ PB * s ^ (-β) := by
    have e1 : (η ^ 2 / s) ^ m * (|η| ^ i * d) = (|η| ^ (2 * m + i) * d) / s ^ m := by
      rw [div_pow, ← pow_mul, show η ^ (2 * m) = |η| ^ (2 * m) by
        rw [pow_mul, pow_mul, sq_abs]]
      rw [pow_add]
      ring
    have e2 : s ^ k / s ^ m * s ^ ((m : ℝ) - β - k) = s ^ (-β) := by
      rw [← Real.rpow_natCast s k, ← Real.rpow_natCast s m, ← Real.rpow_sub hs0,
        ← Real.rpow_add hs0]
      congr 1; ring
    calc s ^ k * ((η ^ 2 / s) ^ m * (|η| ^ i * d))
        = s ^ k / s ^ m * (|η| ^ (2 * m + i) * d) := by rw [e1]; ring
      _ ≤ s ^ k / s ^ m * (PB * s ^ ((m : ℝ) - β - k)) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = PB * (s ^ k / s ^ m * s ^ ((m : ℝ) - β - k)) := by ring
      _ = PB * s ^ (-β) := by rw [e2]
  have ht : 0 ≤ η ^ 2 / s := by positivity
  have hsβ : 0 ≤ s ^ (-β) := Real.rpow_nonneg hs0.le _
  have hPAB : PA + PB ≤ polyConst (max CA 0 + max CB 0) (MA + MB) ν (ν ^ (-ρ)) := by
    rw [hPA, hPB]
    unfold polyConst
    have hX : 1 ≤ 1 + ν ^ (-ρ) + ν⁻¹ := by
      have : 0 < ν⁻¹ := inv_pos.2 hν
      linarith
    have h1 : CA * (1 + ν ^ (-ρ) + ν⁻¹) ^ MA ≤ max CA 0 * (1 + ν ^ (-ρ) + ν⁻¹) ^ (MA + MB) :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX (Nat.le_add_right _ _))
          (le_max_right _ _))
    have h2 : CB * (1 + ν ^ (-ρ) + ν⁻¹) ^ MB ≤ max CB 0 * (1 + ν ^ (-ρ) + ν⁻¹) ^ (MA + MB) :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX (Nat.le_add_left _ _))
          (le_max_right _ _))
    nlinarith [h1, h2]
  calc (1 + η ^ 2 / s) ^ m * (|η| ^ i * s ^ k * d)
      ≤ (2 ^ m * (1 + (η ^ 2 / s) ^ m)) * (|η| ^ i * s ^ k * d) :=
        mul_le_mul_of_nonneg_right (pow_one_add_le m ht) (by positivity)
    _ = 2 ^ m * (s ^ k * (|η| ^ i * d) + s ^ k * ((η ^ 2 / s) ^ m * (|η| ^ i * d))) := by ring
    _ ≤ 2 ^ m * (PA * s ^ (-β) + PB * s ^ (-β)) :=
        mul_le_mul_of_nonneg_left (add_le_add k1 k2) (by positivity)
    _ = 2 ^ m * (PA + PB) * s ^ (-β) := by ring
    _ ≤ 2 ^ m * polyConst (max CA 0 + max CB 0) (MA + MB) ν (ν ^ (-ρ)) * s ^ (-β) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPAB (by positivity)) hsβ
    _ = polyConst (2 ^ m * (max CA 0 + max CB 0)) (MA + MB) ν (ν ^ (-ρ)) * s ^ (-β) := by
        unfold polyConst; ring

/-! ### The conditional theorem -/

/-- **`PartII-a:R02/3`, conditional** (`LateMeanRemainder`). -/
theorem lateMeanRemainder_of_sub (hK : KExpansion) (hC : ProfileIterComm) (hD : ProfileDict)
    (hSm : MeanRemainderSmooth) (hPt : MeanRemPointwise) : LateMeanRemainder := by
  intro ρ N m b ℓ hρ
  let ι : Type := Σ ν : ℝ, {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)) // UnforcedLeray.Short.PartI.IsBUCTrain tr} × ProfilePoint
  have key := late_assembly (ι := ι) hK hC
    (fun j => 0 < j.1 ∧ 1 ≤ j.2.2.2.2) (fun j => j.1) (fun j => j.1 ^ (-ρ))
    (fun j => j.2.2)
    (fun j => trainProfile fun s z => meanRemainder j.2.1.1 N s z.2)
    (fun _ j => j.2.2.2.2 ^ (-(((b : ℝ) + 2 * N + 3) / 2)))
    (fun _ j hj => Real.rpow_nonneg (by linarith [hj.2]) _)
    (fun _ _ _ _ _ _ => le_rfl)
    (fun j hj => ⟨hj.1, Real.rpow_pos_of_pos hj.1 _, hj.2⟩)
    (by
      rintro ⟨ν, ⟨tr, hb⟩, x⟩ ⟨hν, _⟩
      exact contDiffOn_trainProfile_of_eta
        (hSm ν (ν ^ (-ρ)) hν (Real.rpow_pos_of_pos hν _) tr hb N))
    ℓ b 0 m
    (by
      intro i k
      obtain ⟨C, M, ν₀, hν₀, H⟩ := meanRemTerm_of hPt ρ N m b i k hρ
      refine ⟨C, M, 1, ν₀, one_pos, hν₀, ?_⟩
      rintro ⟨ν, ⟨tr, hb⟩, x⟩ ⟨hν, hx⟩ hνν₀
      have hs0 : 0 < x.2.2 := by linarith
      have hFs := contDiffOn_trainProfile_of_eta
        (hSm ν (ν ^ (-ρ)) hν (Real.rpow_pos_of_pos hν _) tr hb N)
      have hdict := hD _ hFs (i + b) 0 k x hs0
      simp only [iteratedDeriv_zero] at hdict
      show (1 + x.2.1 ^ 2 / x.2.2) ^ m * (|x.2.1| ^ i * x.2.2 ^ k *
          |(partialEta^[i + b] (partialQ^[0] (partialAge^[k]
            (trainProfile fun s z => meanRemainder tr N s z.2)))) x|) ≤
        polyConst C M ν (ν ^ (-ρ)) * x.2.2 ^ (-(((b : ℝ) + 2 * N + 3) / 2))
      rw [hdict]
      exact H ν hν hνν₀ tr hb x.2.2 x.2.1 hx)
  obtain ⟨C, M, κ, ν₀, hκ, hν₀, H⟩ := key
  refine ⟨C, M, ν₀, hν₀, ?_⟩
  intro ν hν hνν₀ tr hb x hx
  exact H ⟨ν, ⟨tr, hb⟩, x⟩ ⟨hν, hx⟩ hνν₀

end UnforcedLeray.Short.PartIIa
