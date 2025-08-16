/-
Copyright (c) 2025 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-
# Convergence of Fejér Sums in $L^1$

This file presents a proof of the result that for any Lebesgue integrable function $f$ on the circle ($f \in L^1(S^1)$),
its sequence of Fejér sums, $\sigma_n(f)$, converges to $f$ in the $L^1$ norm.

The proof hinges on representing the Fejér sum as the convolution of the function $f$ with the Fejér kernel $fejerKernel_n$,
i.e., $\sigma_n(f) = f ⋆ fejerKernel_n$. Convergence is then established by showing that the family of Fejér kernels $\{fejerKernel_n\}$ constitutes an approximation to the identity.

We will demonstrate the crucial properties of the Fejér kernel that make it a "good kernel":
1. Unit Integral: The total integral of the kernel is always 1.
2. Positivity: The kernel is non-negative, a key advantage over the Dirichlet kernel.
3. Concentration of Mass: The kernel's mass becomes increasingly concentrated at the origin as $n \to \infty$.

The final step of the proof uses these properties, along with the continuity of translation in the $L^1$ norm (i.e., $\|\tau_y f - f\|_{L^1} \to 0$ as $y \to 0$).
We express the norm of the difference $\|\sigma_n(f) - f\|_{L^1}$ as an integral involving $f$ and $fejerKernel_n$. By strategically splitting this integral,
we show that the contributions from both a small neighborhood of the origin and its complement can be made arbitrarily small for large $n$, which proves the theorem.
-/

open Real MeasureTheory Filter Finset

-- Define Fejer kernel functions
noncomputable def fejerKernel : ℕ → ℝ → ℂ := fun n x => 1 / (n + 1) * ∑ m ∈ range (n + 1), ∑ k ∈ Icc (-m : ℤ) m, Complex.exp (Complex.I * k * x)

-- Prove that $fejerKernel n$ is smooth for all $n$
lemma contDiff_fejerKernel : ∀ n, ContDiff ℝ ⊤ (fejerKernel n) := by
  intro n; unfold fejerKernel
  apply ContDiff.mul; exact contDiff_const
  apply ContDiff.sum; intros; apply ContDiff.sum
  intros; apply ContDiff.cexp; apply ContDiff.mul
  apply ContDiff.mul; any_goals exact contDiff_const
  have : Complex.ofReal = Complex.ofRealCLM := by
    ext; simp only [Complex.ofRealCLM_apply]
  rw [this]; apply ContinuousLinearMap.contDiff

-- Prove a real closed formula of $fejerKernel n$ for $sin (x / 2) ≠ 0$ by induction
lemma fejerKernel_eq_real : ∀ n x, sin (x / 2) ≠ 0 → fejerKernel n x = 1 / (n + 1) * sin ((n + 1) / 2 * x) ^ 2 / sin (x / 2) ^ 2 := by
  intro n x hx; unfold fejerKernel
  rw [← mul_div]; congr 1
  have : ∀ m : ℕ, ∑ k ∈ Icc (-m : ℤ) m, Complex.exp (Complex.I * k * x) = sin ((m + 1 / 2) * x) / sin (x / 2) := by
    intro m; induction m with
    | zero =>
      simp [-Complex.ofReal_sin]; norm_cast; field_simp
    | succ m ih =>
      push_cast [-Complex.ofReal_sin]
      rw [neg_add', ← sum_erase_add _ _ (show (m:ℤ)+1 ∈ Icc ((-m:ℤ)-1) (m+1) by simp; omega)]
      rw [Icc_erase_right, ← sum_erase_add _ _ (show -(m:ℤ)-1 ∈ Ico ((-m:ℤ)-1) (m+1) by simp; omega)]
      rw [Ico_erase_left, Ioo_sub_one_left_eq_Ioc, Ico_add_one_right_eq_Icc]
      rw [ih, add_assoc, mul_assoc, mul_assoc]
      nth_rw 2 [mul_comm]; nth_rw 4 [mul_comm]
      rw [Complex.exp_mul_I, Complex.exp_mul_I]; norm_cast
      rw [← neg_add', Int.cast_neg, neg_mul, cos_neg, sin_neg, Complex.ofReal_neg]
      rw [neg_mul, ← sub_eq_add_neg]; push_cast [-Complex.ofReal_sin, -Complex.ofReal_cos]
      rw [sub_add_add_cancel]; norm_cast; push_cast
      rw [← eq_sub_iff_add_eq', div_sub_div_same, sin_sub_sin]
      ring_nf; nth_rw 2 [mul_assoc]; rw [mul_inv_cancel₀, mul_one]
      field_simp; exact hx
  replace this : ∀ m ∈ range (n + 1), ∑ k ∈ Icc (-m : ℤ) m, Complex.exp (Complex.I * k * x) = sin ((m + 1 / 2) * x) / sin (x / 2) := by
    intros; apply this
  rw [sum_congr rfl this, ← sum_div]; norm_cast; push_cast
  rw [← mul_div_mul_left _ _ hx, mul_sum]
  replace this : ∀ i ∈ range (n + 1), sin (x / 2) * sin ((i + 1 / 2) * x) = 1 / 2 * (cos (i * x) - cos (((i + 1) : ℕ) * x)) := by
    intro i _; push_cast
    rw [one_div_mul_eq_div, eq_div_iff]
    nth_rw 2 3 [show (i:ℝ) = i+1/2-1/2 by ring]
    set t := (i : ℝ) + 1 / 2 with ht; clear_value t
    rw [sub_mul, show t-1/2+1 = t+1/2 by ring, add_mul, one_div_mul_eq_div]
    rw [cos_add, cos_sub]; ring; norm_num
  rw [sum_congr rfl this, ← mul_sum, sum_range_sub']
  simp [-one_div]; rw [mul_one_sub, one_div_mul_eq_div]
  rw [show (n+1)*x = 2*((n+1)/2*x) by ring, ← sin_sq_eq_half_sub, ← pow_two]

-- Compute the integral of $fejerKernel$ in $[-π, π]$
lemma integral_fejerKernel : ∀ n, ∫ x in (-π)..π, fejerKernel n x = 2 * π := by
  intro n; unfold fejerKernel
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finset_sum]
  have : ∀ x ∈ range (n + 1), ∫ (x_1 : ℝ) in -π..π, ∑ k ∈ Icc (-x : ℤ) x, Complex.exp (Complex.I * k * x_1) = 2 * π := by
    intro x hx; simp at hx
    rw [intervalIntegral.integral_finset_sum, ← sum_erase_add _ _ (show 0 ∈ Icc (-x:ℤ) x by simp)]
    set s := (Icc (-x : ℤ) x).erase 0 with hs; clear_value s
    simp [← eq_sub_iff_add_eq]; ring_nf; apply sum_eq_zero
    intro i hi; simp [hs] at hi
    have : Set.EqOn (fun (x : ℝ) => Complex.exp (Complex.I * i * x) ) (fun x => cos (i * x) + Complex.I * sin (i * x)) (Set.uIcc (-π) π) := by
      intro x _; simp; rw [mul_assoc, mul_comm]
      norm_cast; simp [Complex.exp_mul_I]; ring
    rw [intervalIntegral.integral_congr this, intervalIntegral.integral_add]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
    simp [Complex.ext_iff]; constructor
    · rw [intervalIntegral.integral_comp_mul_left]; simp
      norm_cast; exact hi.left
    · rw [intervalIntegral.integral_comp_mul_left]; simp
      norm_cast; exact hi.left
    any_goals apply Continuous.intervalIntegrable; fun_prop
    · intros; apply Continuous.intervalIntegrable; fun_prop
  simp [sum_congr rfl this]; rw [← mul_assoc, inv_mul_cancel₀, one_mul]
  · norm_cast
  · intro i hi; apply Continuous.intervalIntegrable; fun_prop

-- Prove an auxillary fact that $sin (x / 2) = 0$ if and only if $x = 0$ when $x$ belongs to $[-π, π]$
lemma aux_sin : ∀ x ∈ Set.Icc (-π) π, sin (x / 2) = 0 ↔ x = 0 := by
  intro x hx; simp at hx
  rw [sin_eq_zero_iff]; constructor
  · rintro ⟨n, hn⟩; rw [eq_div_iff] at hn; rw [← hn] at hx
    rcases hx with ⟨hx1, hx2⟩
    nth_rw 2 [mul_comm] at hx1 hx2; rw [mul_assoc] at hx1 hx2
    rw [← mul_neg_one, mul_le_mul_left] at hx1; norm_cast at hx1
    nth_rw 2 [← mul_one π] at hx2; rw [mul_le_mul_left] at hx2
    norm_cast at hx2; simp at hx1; simp [← hn]
    left; omega
    all_goals positivity
  intro; use 0; symm; simp; assumption

-- Prove that the integral of the norm of $fejerKernel$ in $[-π, π]$ is $2 * π$
lemma integral_norm_fejerKernel : ∀ n, ∫ x in (-π)..π, ‖fejerKernel n x‖ = 2 * π := by
  intro n; calc
  _ = ∫ x in (-π)..π, 1 / (n + 1) * sin ((n + 1) / 2 * x) ^ 2 / sin (x / 2) ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    rw [ae_iff, show (0:ENNReal) = volume {(0:ℝ)} by simp]; congr 1
    simp only [Classical.not_imp, Set.ext_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    intro x; rw [Set.uIoc_eq_union]; nth_rw 2 [Set.Ioc_eq_empty]
    rw [Set.union_empty]; constructor
    · rintro ⟨xmem, hx⟩; revert hx; contrapose!
      intro hx; rw [fejerKernel_eq_real, ← mul_div, norm_mul, norm_div]
      norm_cast; push_cast [Real.norm_eq_abs]
      rw [abs_eq_self.mpr, mul_div]; positivity
      · intro h; rw [aux_sin] at h; contradiction
        apply Set.mem_Icc_of_Ioc; exact xmem
    intro hx; unfold fejerKernel; simp [hx]
    split_ands; any_goals norm_cast
    any_goals positivity
    linarith only [pi_pos]
  _ = _ := by
    rw [← Complex.ofReal_inj, intervalIntegral]; push_cast
    rw [← integral_fejerKernel n]; simp only [← integral_complex_ofReal]
    rw [← intervalIntegral]; apply intervalIntegral.integral_congr_ae
    rw [ae_iff, show (0:ENNReal) = volume {(0:ℝ)} by simp]; congr 1
    simp only [Classical.not_imp, Set.ext_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    intro x; rw [Set.uIoc_eq_union]; nth_rw 2 [Set.Ioc_eq_empty]
    rw [Set.union_empty]; constructor
    · rintro ⟨xmem, hx⟩; revert hx; contrapose!
      intro hx; rw [fejerKernel_eq_real]; push_cast; rfl
      · intro h; rw [aux_sin] at h; contradiction
        apply Set.mem_Icc_of_Ioc; exact xmem
    intro hx; unfold fejerKernel; simp [hx]
    split_ands; any_goals norm_cast
    any_goals positivity
    linarith only [pi_pos]

-- Prove the concentration of mass property of the integral of $fejerKernel n$
lemma fejerKernel_mass : ∀ δ > 0, δ < π → Tendsto (fun n => ∫ x in (setOf fun x => δ ≤ |x| ∧ |x| ≤ π), fejerKernel n x) atTop (nhds 0) := by
  intro δ δpos δlt; rw [Metric.tendsto_atTop]
  have ne_top : volume (Set.Icc (-π) π) ≠ ⊤ := by simp
  have aux_sbst : Set.Ioo (-δ) δ ⊆ Set.Icc (-π) π := by
    simp [Set.subset_def]
    intros; exact ⟨by linarith, by linarith⟩
  intro ε εpos; simp
  set S := setOf fun x => δ ≤ |x| ∧ |x| ≤ π with hS; clear_value S
  have S_eq : S = Set.Icc (-π) π \ Set.Ioo (-δ) δ := by
    simp only [hS, Set.ext_iff, Set.mem_setOf_eq, Set.mem_diff, Set.mem_Icc, Set.mem_Ioo, not_and, not_lt]
    intro x; rw [and_comm, abs_le, le_abs]
    simp only [and_congr_right_iff, and_imp]
    intros; rw [le_neg, Classical.or_iff_not_imp_right, not_le]
  have S_vol : volume S ≠ ⊤ := by
    rw [S_eq, measure_diff]; any_goals simp
    · exact aux_sbst
  have S_mea : MeasurableSet S := by
    rw [S_eq]; apply MeasurableSet.diff
    exact measurableSet_Icc; exact measurableSet_Ioo
  have aux_ge : ∀ x ∈ S, sin (δ / 2) ^ 2 ≤ sin (x / 2) ^ 2 := by
    intro x hx; simp [hS] at hx
    rw [sin_sq_eq_half_sub, sin_sq_eq_half_sub]; gcongr
    norm_num [mul_div_cancel₀]; rw [← cos_abs]; nth_rw 2 [← cos_abs]
    apply cos_le_cos_of_nonneg_of_le_pi
    positivity; exact hx.right
    · rw [abs_eq_self.mpr]; exact hx.left
      positivity
  use ⌊2 * π / (ε * sin (δ / 2) ^ 2)⌋₊ + 1; intro n nge
  have : Set.EqOn (fejerKernel n) (fun x => 1 / (n + 1) * sin ((n + 1) / 2 * x) ^ 2 / sin (x / 2) ^ 2) S := by
    intro x hx; simp [hS] at hx; rw [fejerKernel_eq_real]
    · intro h; rw [aux_sin] at h
      simp [h] at hx; linarith only [hx.left, δpos]
      · rw [Set.mem_Icc, ← abs_le]; exact hx.right
  rw [setIntegral_congr_fun _ this]; simp_rw [← mul_div]
  rw [integral_const_mul]; norm_cast
  rw [integral_complex_ofReal, norm_mul]
  simp; norm_cast; push_cast; calc
    _ ≤ ((n : ℝ) + 1)⁻¹ * ∫ (x : ℝ) in S, |sin ((n + 1) / 2 * x) ^ 2 / sin (x / 2) ^ 2| := by
      gcongr; apply abs_integral_le_integral_abs
    _ < _ := by
      rw [inv_mul_eq_div, div_lt_iff₀]
      replace this : ∀ x ∈ S, |sin ((n + 1) / 2 * x) ^ 2 / sin (x / 2) ^ 2| ≤ 1 / sin (δ / 2) ^ 2 := by
        intro x hx; simp [hS] at hx
        rw [abs_div, abs_pow]; gcongr
        · rw [sq_pos_iff]; intro h; rw [aux_sin] at h
          simp [h] at δpos
          · rw [Set.mem_Icc]; constructor
            · apply le_of_lt; rw [gt_iff_lt] at δpos
              apply lt_trans _ δpos; simp only [Left.neg_neg_iff]
              positivity
            linarith only [δlt]
        · rw [sq_le_one_iff₀]; apply abs_sin_le_one
          positivity
        · rw [abs_sq, sin_sq_eq_half_sub, sin_sq_eq_half_sub]
          field_simp; gcongr; rw [← cos_abs]
          apply cos_le_cos_of_nonneg_of_le_pi
          positivity; exact hx.right; exact hx.left
      apply lt_of_le_of_lt (setIntegral_mono_on _ _ _ this)
      · rify at nge; replace nge := lt_of_lt_of_le (Nat.lt_floor_add_one _) nge
        simp [integral_const, -one_div]; calc
          _ < volume.real (Set.Icc (-π) π) * (1 / sin (δ / 2) ^ 2) := by
            gcongr
            · simp [sq_pos_iff]; rw [aux_sin]; positivity
              rw [Set.mem_Icc]; constructor
              · apply le_of_lt; rw [gt_iff_lt] at δpos
                apply lt_trans _ δpos; simp only [Left.neg_neg_iff]
                positivity
              linarith only [δlt]
            rw [S_eq, measureReal_diff, sub_lt_self_iff]
            simp; exact δpos; exact aux_sbst
            exact measurableSet_Ioo
          _ < _ := by
            rw [volume_real_Icc, sub_neg_eq_add, ← two_mul, max_eq_left, mul_one_div]
            rw [← div_lt_iff₀', div_div]; nth_rw 2 [mul_comm]
            linarith only [nge]
            all_goals positivity
      · apply ContinuousOn.integrableOn_compact
        · rw [hS]; replace this : setOf fun x => δ ≤ |x| ∧ |x| ≤ π = Set.Icc (-π) (-δ) ∪ Set.Icc δ π := by
            simp [Set.ext_iff]; intro x; rw [le_abs, abs_le]
            constructor
            · rintro ⟨h, ⟨⟩⟩; rcases h with h|h
              · right; constructor; all_goals assumption
              left; exact ⟨by linarith, by linarith⟩
            intro h; rcases h with ⟨_,_⟩|⟨_,_⟩
            · constructor; right; linarith
              exact ⟨by assumption, by linarith⟩
            constructor; left; assumption
            exact ⟨by linarith, by assumption⟩
          rw [this]; apply IsCompact.union
          all_goals exact isCompact_Icc
        apply ContinuousOn.abs; apply ContinuousOn.div
        any_goals fun_prop
        · intro x hx; simp [hS] at hx
          rw [pow_ne_zero_iff, ne_eq, aux_sin]
          intro h; simp [h] at hx
          linarith only [hx.left, δpos]
          · rw [Set.mem_Icc, ← abs_le]; exact hx.right
          positivity
      · apply integrableOn_const; exact S_vol
        simp
      · exact S_mea
      positivity
  exact S_mea

-- Define an auxillary notion `cmul_bl` to be the standard real bilinear forms of complex multiplications on complex numbers
@[continuity]
lemma aux_cont : Continuous fun x : ℂ =>
    ({ toFun := fun y => x * y, map_add' := by intros; ring, map_smul' := by intros; simp; ring, cont := by continuity } : ℂ →L[ℝ] ℂ) := by
  rw [Metric.continuous_iff]
  simp [dist_eq_norm]; intro x ε εpos
  use ε / 2; constructor; positivity
  intros; calc
    _ ≤ ε / 2 := by
      rw [ContinuousLinearMap.opNorm_le_iff]; simp
      intro; rw [← sub_mul, norm_mul]; gcongr; positivity
    _ < _ := by linarith only [εpos]

noncomputable def cmul_bl : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := {
  toFun := fun x => {
    toFun := fun y => x * y
    map_add' := by intros; ring
    map_smul' := by intros; simp; ring
  }
  map_add' := by intros; ext; simp; ring
  map_smul' := by intros; ext; simp; ring
}

lemma aux_cmul : ∀ x y, cmul_bl x y = x * y := by simp [cmul_bl]

-- Prove two auxillary integrablility results
lemma aux_integrable [Fact (0 < 2 * π)] : ∀ n, Integrable (fejerKernel n ∘ Subtype.val ∘ ⇑(AddCircle.measurableEquivIoc (2 * π) (-π))) volume := by
  intro n; rw [← Function.comp_assoc, ← (AddCircle.measurableEquivIoc (2 * π) (-π)).measurableEmbedding.integrable_map_iff]
  rw [← (MeasurableEmbedding.subtype_coe measurableSet_Ioc).integrable_map_iff]
  have : Measure.map Subtype.val (Measure.map (⇑(AddCircle.measurableEquivIoc (2 * π) (-π))) volume) =
  volume.restrict (Set.Ioc (-π) (-π + 2 * π)) := by
    ext s hs; rw [(MeasurableEmbedding.subtype_coe measurableSet_Ioc).map_apply]
    rw [(AddCircle.measurableEquivIoc (2 * π) (-π)).map_apply, Measure.restrict_apply]
    rw [← (AddCircle.measurePreserving_mk (2 * π) (-π)).measure_preimage, Measure.restrict_apply]
    congr 1; simp [Set.ext_iff, AddCircle.measurableEquivIoc, AddCircle.equivIoc]
    intro x _ _; rw [(toIocMod_eq_self _).mpr]
    · rw [Set.mem_Ioc]; constructor
      assumption; linarith
    · apply AddCircle.measurable_mk'; apply (AddCircle.measurableEquivIoc (2 * π) (-π)).measurable
      apply (MeasurableEmbedding.subtype_coe measurableSet_Ioc).measurable; exact hs
    · apply MeasurableSet.nullMeasurableSet; apply (AddCircle.measurableEquivIoc (2 * π) (-π)).measurable
      apply (MeasurableEmbedding.subtype_coe measurableSet_Ioc).measurable; exact hs
    exact hs
  rw [this, ← IntegrableOn]; apply Continuous.integrableOn_Ioc
  exact (contDiff_fejerKernel n).continuous

lemma aux_convolution_integrable [Fact (0 < 2 * π)] : ∀ n, ∀ f : AddCircle (2 * π) → ℂ, Integrable f volume →
    Integrable (convolution ((fejerKernel n) ∘ (Subtype.val) ∘ (AddCircle.measurableEquivIoc (2 * π) (-π))) f cmul_bl volume) volume := by
  intro n f hf; apply Integrable.integrable_convolution
  · exact aux_integrable n
  exact hf

-- Prove two properties of the translation operators on 𝓛¹(AddCircle (2 * π) → ℂ), the first one is the fact that the translation operator preserves 𝓛¹-norm
lemma norm_translation [Fact (0 < 2 * π)] : ∀ f : AddCircle (2 * π) → ℂ, ∀ hf : Integrable f volume, ∀ y,
    ‖(hf.comp_sub_right y).toL1‖ = ‖hf.toL1‖ := by
  intro f hf y; simp only [L1.norm_of_fun_eq_integral_norm]
  have aux_eq : Measure.map (fun a => a - y) volume = volume := by
    ext s hs; rw [Measure.map_apply]
    · simp only [sub_eq_add_neg, measure_preimage_add_right]
    · fun_prop
    exact hs
  have aux_mea : AEMeasurable (fun a => a - y) := by fun_prop
  have aux_smea : AEStronglyMeasurable (fun x => ‖f x‖) (Measure.map (fun a => a - y) volume) := by
    apply AEStronglyMeasurable.comp_aemeasurable
    · apply Continuous.aestronglyMeasurable
      exact continuous_norm
    · rw [aux_eq]; exact hf.aemeasurable
  rw [← integral_map aux_mea aux_smea, aux_eq]

-- Prove that when $y$ goes to zero, the 𝓛¹-norm of the translated functions $f(x-y)$ goes to the 𝓛¹-norm of $f(x)$
lemma tendsto_translation [Fact (0 < 2 * π)] : ∀ f : AddCircle (2 * π) → ℂ, ∀ hf : Integrable f volume,
    Tendsto (fun y => (hf.comp_sub_right y).toL1) (nhds 0) (nhds hf.toL1) := by
  intro f hf; rw [Metric.tendsto_nhds_nhds]
  intro ε εpos; simp only [dist_eq_norm, sub_zero]
  have : Fact ((1 : ENNReal) ≤ 1) := ⟨by rfl⟩
  have := ContinuousMap.toLp_denseRange ℂ (volume : Measure (AddCircle (2 * π))) ℂ (show 1 ≠ ⊤ by simp)
  simp [denseRange_iff_closure_range, Set.ext_iff, Metric.mem_closure_iff, dist_eq_norm] at this
  specialize this hf.toL1 hf.toL1.mem (ε / 3) (by positivity)
  rcases this with ⟨g, hg⟩
  have aux_g : ∀ y, Integrable (g ∘ (fun x => x - y)) := by
    intro; apply Continuous.integrable_of_hasCompactSupport
    apply Continuous.comp
    · exact g.continuous
    · fun_prop
    apply HasCompactSupport.of_compactSpace
  have int_g := aux_g 0
  rw [show (⇑g ∘ fun x => x - 0) = ⇑g by ext; simp] at int_g
  have := g.uniform_continuity
  specialize this (ε / (6 * π)) (by positivity); rcases this with ⟨δ, δpos, hδ⟩
  simp only [dist_eq_norm] at hδ
  use δ; constructor; exact δpos
  intro y nylt; calc
    _ = ‖Integrable.toL1 (fun x => f (x - y)) (hf.comp_sub_right y) - (aux_g y).toL1 + ((aux_g y).toL1 - int_g.toL1) + (int_g.toL1 - hf.toL1)‖ := by
      rw [sub_add_sub_cancel, sub_add_sub_cancel]
    _ ≤ _ := norm_add₃_le
    _ < _ := by
      rw [show ε = ε / 3 + ε / 3 + ε / 3 by ring]; gcongr
      · rw [← Integrable.toL1_sub]
        have : ((fun x => f (x - y)) - ⇑g ∘ fun x => x - y) = fun x => (f - g) (x - y) := by
          ext; simp only [Pi.sub_apply, Function.comp_apply]
        simp only [this]; rw [norm_translation]
        · rw [Integrable.toL1_sub]; exact hg; exact hf
          apply Continuous.integrable_of_hasCompactSupport
          exact ContinuousMap.continuous g
          apply HasCompactSupport.of_compactSpace
      · rw [← Integrable.toL1_sub, L1.norm_of_fun_eq_integral_norm]
        simp only [Pi.sub_apply, Function.comp_apply]
        have : ε / 3 = ∫ (a : AddCircle (2 * π)), ε / (6 * π) ∂volume := by
          simp only [integral_const, measureReal_def, AddCircle.measure_univ, smul_eq_mul]
          rw [ENNReal.toReal_ofReal]; field_simp; ring
          positivity
        rw [this, ← sub_pos, ← integral_sub, integral_pos_iff_support_of_nonneg]
        · suffices : Function.support (fun a => ε / (6 * π) - ‖g (a - y) - g a‖) = Set.univ
          · rw [this, AddCircle.measure_univ]; positivity
          simp [Set.ext_iff]; intro x
          apply ne_of_gt; rw [sub_pos]; apply hδ
          rw [sub_right_comm, sub_self, zero_sub, norm_neg]
          exact nylt
        · simp [Pi.le_def]; intro x
          apply le_of_lt; apply hδ
          rw [sub_right_comm, sub_self, zero_sub, norm_neg]
          exact nylt
        · apply Integrable.sub; apply integrable_const
          apply Integrable.norm; apply Integrable.sub
          apply aux_g; exact int_g
        · apply integrable_const
        · apply Integrable.norm; apply Integrable.sub
          apply aux_g; exact int_g
      · rw [norm_sub_rev]; exact hg

-- The main theorem of 𝓛¹-convergence of Fejer sum for Lebesgue integrable functions
theorem Fejer_L1 [Fact (0 < 2 * π)] : ∀ f : AddCircle (2 * π) → ℂ, ∀ hf : Integrable f volume,
    Tendsto (fun n => (aux_convolution_integrable n f hf).toL1) atTop (nhds ((2 * π) • hf.toL1)) := by
  intro f hf; rw [Metric.tendsto_atTop]
  intro ε εpos; simp only [dist_eq_norm, ← Integrable.toL1_smul, ← Integrable.toL1_sub]
  simp only [L1.norm_of_fun_eq_integral_norm, Pi.sub_apply, convolution_def, aux_cmul]
  have := tendsto_translation f hf
  rw [Metric.tendsto_nhds_nhds] at this
  specialize this (ε / (4 * π)) (by positivity)
  rcases this with ⟨δ, δpos, hδ⟩
  simp only [dist_eq_norm, sub_zero, ← Integrable.toL1_sub] at hδ
  simp only [L1.norm_of_fun_eq_integral_norm, Pi.sub_apply] at hδ
  have := fejerKernel_mass (δ ⊓ π / 2) (by positivity) (lt_of_le_of_lt (min_le_right _ _) (by linarith only [pi_pos]))
  simp only [Metric.tendsto_atTop, dist_eq_norm, sub_zero] at this
  specialize this (ε / (4 * ‖hf.toL1‖ + 1)) (by positivity)
  rcases this with ⟨N, hN⟩
  have aux_sbst : Set.Ioo (-(δ ⊓ π / 2)) (δ ⊓ π / 2) ⊆ Set.Icc (-π) π := by
    simp [Set.subset_def]; intros; constructor
    all_goals linarith [min_le_right δ (π / 2)]
  set S := setOf fun x => δ ⊓ π / 2 ≤ |x| ∧ |x| ≤ π with hS; clear_value S
  have S_eq : S = Set.Icc (-π) π \ Set.Ioo (-(δ ⊓ π / 2)) (δ ⊓ π / 2) := by
    simp only [hS, Set.ext_iff, Set.mem_setOf_eq, Set.mem_diff, Set.mem_Icc, Set.mem_Ioo, not_and, not_lt]
    intro x; rw [and_comm, abs_le, le_abs]
    simp only [and_congr_right_iff, and_imp]
    intros; rw [le_neg, Classical.or_iff_not_imp_right, not_le]
  have S_cpt : IsCompact S := by
    suffices : S = Set.Icc (-π) (-(min δ (π / 2))) ∪ Set.Icc (min δ (π / 2)) π
    · rw [this]; apply IsCompact.union
      all_goals exact isCompact_Icc
    ext x; simp only [hS, Set.mem_setOf, Set.mem_union, Set.mem_Icc, le_abs, abs_le]
    constructor
    · rintro ⟨h, ⟨⟩⟩; rcases h with h|h
      · right; constructor
        all_goals assumption
      left; constructor; assumption; linarith
    intro h; rcases h with ⟨_,h⟩|⟨h,_⟩
    · constructor; right; linarith
      constructor; assumption
      apply le_trans h; apply le_of_lt
      apply lt_trans _ pi_pos; rw [neg_lt, neg_zero]
      positivity
    constructor; left; assumption
    constructor
    · apply le_trans _ h; apply le_of_lt; calc
        _ < (0 : ℝ) := by
          rw [neg_lt, neg_zero]; positivity
        _ < _ := by positivity
    assumption
  have aux : IntegrableOn (fun x : ℝ => ∫ (a_1 : AddCircle (2 * π)), ‖f (a_1 - x) - f a_1‖) (Set.Ioc (-π) (-π + 2 * π)) volume := by
    rw [integrableOn_iff_comap_subtypeVal]
    have : ((fun x : ℝ => ∫ (a_1 : AddCircle (2 * π)), ‖f (a_1 - x) - f a_1‖) ∘ @Subtype.val ℝ fun x => x ∈ Set.Ioc (-π) (-π + 2 * π)) =
    ((fun u => ∫ (a_1 : AddCircle (2 * π)), ‖f (a_1 - u) - f a_1‖) ∘ QuotientAddGroup.mk) ∘ Subtype.val := by
      ext; simp only [Function.comp_apply]
    rw [this, ← (MeasurableEmbedding.subtype_coe _).integrableOn_range_iff_comap, IntegrableOn]
    simp only [Subtype.range_coe_subtype, Set.setOf_mem_eq]
    rw [(AddCircle.measurePreserving_mk (2 * π) (-π)).integrable_comp]
    set F := fun (x, y) => f (x - y) - f x with hF
    simp only [funext_iff, Prod.forall] at hF; simp only [← hF]
    apply Integrable.integral_norm_prod_right
    dsimp [F]; apply Integrable.sub
    · replace this : Integrable (fun _ => (1 : ℂ)) (volume : Measure (AddCircle (2 * π))) := by
        apply integrable_const
      have aux_conv := Integrable.convolution_integrand cmul_bl this hf
      simp [aux_cmul] at aux_conv; exact aux_conv
    · replace this : (fun x : AddCircle (2 * π) × AddCircle (2 * π) => f x.1) =
      fun x => f x.1 * (1 : AddCircle (2 * π) → ℂ) x.2 := by
        ext; simp
      rw [this]; apply Integrable.mul_prod; exact hf
      apply integrable_const
    · set F := fun (x, y) => ‖f (y - x) - f y‖ with hF
      simp only [funext_iff, Prod.forall] at hF; simp only [← hF]
      apply AEStronglyMeasurable.integral_prod_right'
      dsimp [F]; apply AEStronglyMeasurable.norm
      apply AEStronglyMeasurable.sub
      · replace this : AEStronglyMeasurable (fun _ => (1 : ℂ)) (volume : Measure (AddCircle (2 * π)))
        := aestronglyMeasurable_const
        have aux_conv := AEStronglyMeasurable.convolution_integrand cmul_bl this hf.aestronglyMeasurable
        simp only [aux_cmul, one_mul] at aux_conv
        apply AEStronglyMeasurable.prod_swap at aux_conv
        exact aux_conv
      exact hf.aestronglyMeasurable.comp_snd
    all_goals exact measurableSet_Ioc
  use N; intro n nge
  specialize hN n nge; calc
    _ ≤ ∫ (a : AddCircle (2 * π)), ∫ t : AddCircle (2 * π), ‖(fejerKernel n ∘ Subtype.val ∘ ⇑(AddCircle.measurableEquivIoc (2 * π) (-π))) t‖ * ‖f (a - t) - f a‖ := by
      apply integral_mono
      · apply Integrable.norm; apply Integrable.sub
        · exact aux_convolution_integrable n f hf
        · apply Integrable.smul; exact hf
      · set F := fun (x, t) => (fejerKernel n ∘ Subtype.val ∘ ⇑(AddCircle.measurableEquivIoc (2 * π) (-π))) t * (f (x - t) - f x) with hF
        simp only [funext_iff, Prod.forall] at hF
        simp only [← norm_mul, ← hF]
        apply Integrable.integral_norm_prod_left
        simp only [F, mul_sub]; apply Integrable.sub
        · exact Integrable.convolution_integrand cmul_bl (aux_integrable n) hf
        · simp_rw [mul_comm]; apply Integrable.mul_prod
          exact hf; exact aux_integrable n
      rw [Pi.le_def]; intro x
      have : (2 * π) • f x = ∫ (t : AddCircle (2 * π)), (fejerKernel n ∘ Subtype.val ∘ ⇑(AddCircle.measurableEquivIoc (2 * π) (-π))) t * f x := by
        simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat, ← integral_fejerKernel n, ← intervalIntegral.integral_mul_const]
        rw [← AddCircle.integral_preimage _ (-π), intervalIntegral]
        nth_rw 2 [Set.Ioc_eq_empty]; simp [show -π+2*π = π by ring]
        simp [AddCircle.measurableEquivIoc, AddCircle.equivIoc]
        apply setIntegral_congr_fun; exact measurableSet_Ioc
        · intro a ha; simp only [mul_eq_mul_right_iff]; left
          congr 1; symm; rw [toIocMod_eq_self]
          convert ha; ring
        linarith only [pi_pos]
      simp only [this, ← norm_mul]; rw [← integral_sub]
      simp only [← mul_sub]; apply norm_integral_le_integral_norm
      · rw [← (AddCircle.measurePreserving_mk (2 * π) (-π)).integrable_comp, ← IntegrableOn]
        set F := (fun t => (fejerKernel n ∘ Subtype.val ∘ ⇑(AddCircle.measurableEquivIoc (2 * π) (-π))) t * f (x - t)) ∘ QuotientAddGroup.mk
        suffices : Set.EqOn F (fun t => (fejerKernel n t) * f (x - t)) ((Set.Ioc (-π) (-π + 2 * π)))
        · rw [integrableOn_congr_fun this measurableSet_Ioc, ← integrableOn_Icc_iff_integrableOn_Ioc]
          apply IntegrableOn.continuousOn_mul
          · apply Continuous.continuousOn
            exact (contDiff_fejerKernel n).continuous
          rw [integrableOn_Icc_iff_integrableOn_Ioc]
          have : Set.EqOn (fun y : ℝ => f (x - y)) ((fun y => f (x - y)) ∘ QuotientAddGroup.mk) (Set.Ioc (-π) (-π + 2 * π)) := by
            intro; simp
          rw [integrableOn_congr_fun this measurableSet_Ioc, IntegrableOn]
          rw [(AddCircle.measurePreserving_mk (2 * π) (-π)).integrable_comp]
          apply hf.comp_sub_left; exact (hf.comp_sub_left x).aestronglyMeasurable
          exact isCompact_Icc
        intro y hy; simp [F, AddCircle.measurableEquivIoc, AddCircle.equivIoc]
        left; rw [(toIocMod_eq_self _).mpr hy]
        · apply AEStronglyMeasurable.mul
          · apply AEStronglyMeasurable.comp_measurable
            · apply Continuous.aestronglyMeasurable
              exact (contDiff_fejerKernel n).continuous
            apply Measurable.comp
            · exact measurable_subtype_coe
            exact (AddCircle.measurableEquivIoc (2 * π) (-π)).measurable
          exact (hf.comp_sub_left x).aestronglyMeasurable
      apply Integrable.mul_const; exact aux_integrable n
    _ = ∫ (a : ℝ) in Set.Ioc (-π) π, ‖fejerKernel n a‖ * ∫ (a_1 : AddCircle (2 * π)), ‖f (a_1 - ↑a) - f a_1‖ := by
      rw [integral_integral_swap]; simp only [integral_const_mul]
      rw [← AddCircle.integral_preimage _ (-π)]
      simp [show -π+2*π = π by ring, AddCircle.measurableEquivIoc, AddCircle.equivIoc]
      apply setIntegral_congr_fun; exact measurableSet_Ioc
      · intro a ha; simp only [mul_eq_mul_right_iff]; left
        congr; rw [toIocMod_eq_self]
        convert ha; ring
      simp only [← norm_mul, mul_sub]; apply Integrable.norm
      apply Integrable.sub
      · exact Integrable.convolution_integrand cmul_bl (aux_integrable n) hf
      · simp_rw [mul_comm]; apply Integrable.mul_prod
        exact hf; exact aux_integrable n
    _ < _ := by
      rw [← integral_Icc_eq_integral_Ioc, ← Set.diff_union_of_subset aux_sbst]
      rw [setIntegral_union, ← S_eq, show ε = ε / 2 + ε / 2 by ring]; gcongr
      · calc
          _ ≤ ∫ (x : ℝ) in S, ‖fejerKernel n x‖ * (2 * ‖hf.toL1‖) := by
            apply setIntegral_mono_on
            · apply IntegrableOn.continuousOn_mul
              · apply ContinuousOn.norm; apply Continuous.continuousOn
                exact (contDiff_fejerKernel n).continuous
              · rw [S_eq]; apply IntegrableOn.mono _ Set.diff_subset (by rfl)
                rw [show Set.Icc (-π) π = Set.Icc (-π) (-π + 2 * π) by ring_nf]
                rw [integrableOn_Icc_iff_integrableOn_Ioc]; exact aux
              exact S_cpt
            · rw [IntegrableOn]; apply Integrable.mul_const
              apply Integrable.norm; rw [← IntegrableOn]
              apply ContinuousOn.integrableOn_compact S_cpt
              apply Continuous.continuousOn; exact (contDiff_fejerKernel n).continuous
            · rw [S_eq]; apply MeasurableSet.diff
              exact measurableSet_Icc; exact measurableSet_Ioo
            · intro x hx; gcongr
              suffices : ∫ (a_1 : AddCircle (2 * π)), ‖f (a_1 - x) - f a_1‖ = ‖(hf.comp_sub_right x).toL1 - hf.toL1‖
              · rw [this, two_mul (‖Integrable.toL1 f hf‖)]
                nth_rw 1 [← norm_translation f hf x]; apply norm_sub_le
              rw [← Integrable.toL1_sub, L1.norm_of_fun_eq_integral_norm]
              simp only [Pi.sub_apply]
          _ < _ := by
            rw [integral_mul_const]
            suffices : Set.EqOn (fejerKernel n) (fun x => (1 / (n + 1) * sin ((n + 1) / 2 * x) ^ 2 / sin (x / 2) ^ 2)) S
            · rw [setIntegral_congr_fun _ this] at hN
              simp only [← mul_div, integral_const_mul, norm_mul, norm_div] at hN
              norm_cast at hN; simp only [integral_complex_ofReal, Complex.norm_real] at hN
              replace this : Set.EqOn (fun x => ‖fejerKernel n x‖) (fun x => (1 / (n + 1) * sin ((n + 1) / 2 * x) ^ 2 / sin (x / 2) ^ 2)) S := by
                intro y hy; rw [Set.EqOn] at this
                specialize this hy; simp only [this, ← mul_div, ← Complex.ofReal_pow, ← Complex.ofReal_div]
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; congr 1
                · rw [norm_div]; norm_cast
                · rw [abs_eq_self]; positivity
              rw [setIntegral_congr_fun _ this]
              by_cases h : ‖Integrable.toL1 f hf‖ = 0
              · simp [h]; exact εpos
              rw [Real.norm_eq_abs, abs_eq_self.mpr] at hN; push_cast at hN
              rw [← lt_div_iff₀, div_div]; simp only [← mul_div, integral_const_mul]
              apply lt_trans hN; gcongr
              rw [← sub_pos]; ring_nf; any_goals positivity
              all_goals rw [S_eq]; apply MeasurableSet.diff
              any_goals exact measurableSet_Icc
              all_goals exact measurableSet_Ioo
            intro y hy; rw [fejerKernel_eq_real]; intro h
            rw [aux_sin] at h; simp only [hS, Set.mem_setOf, h, abs_zero] at hy
            replace hy := hy.left; revert hy
            rw [imp_false, not_le]; positivity
            · rw [S_eq] at hy; apply Set.diff_subset at hy
              exact hy
      calc
        _ < ∫ (x : ℝ) in Set.Ioo (-min δ (π / 2)) (min δ (π / 2)), ‖fejerKernel n x‖ * (ε / (4 * π)) := by
          rw [← sub_pos, ← integral_sub, setIntegral_pos_iff_support_of_nonneg_ae]
          · rw [Set.inter_comm, measure_inter_conull', volume_Ioo, ENNReal.ofReal_pos]
            ring_nf; positivity
            · suffices : volume (setOf fun x => |x| < δ ⊓ (π / 2) ∧ fejerKernel n x = 0) = 0
              · rw [← this]; congr 1
                simp only [Set.ext_iff, Set.mem_diff, Set.mem_Ioo, ← abs_lt, Function.notMem_support, Set.mem_setOf]
                simp only [and_congr_right_iff]; intro x hx
                rw [← mul_sub, mul_eq_zero_iff_right]; exact norm_eq_zero
                · apply ne_of_gt; rw [sub_pos]; apply hδ
                  rw [(AddCircle.norm_coe_eq_abs_iff (2 * π) (by positivity)).mpr]
                  apply lt_of_lt_of_le hx; apply min_le_left
                  · nth_rw 2 [abs_eq_self.mpr]; norm_num
                    apply le_of_lt; apply lt_trans hx
                    apply lt_of_le_of_lt (min_le_right _ _)
                    linarith only [pi_pos]; positivity
              let F : ℤ → ℝ := fun k => 2 * k / (n + 1) * π
              have aux_sbst : {x | |x| < min δ (π / 2) ∧ fejerKernel n x = 0} ⊆ F '' (setOf fun x => |x| ≤ ⌊(n + 1) * (δ ⊓ (π / 2)) / (2 * π)⌋) := by
                simp only [Set.subset_def, Set.mem_setOf, Set.mem_image, F]
                rintro x ⟨hx1, hx2⟩; have : x ≠ 0 := by
                  intro h; revert hx2; rw [imp_false]
                  unfold fejerKernel; simp [h]; constructor
                  all_goals norm_cast
                  positivity
                rw [fejerKernel_eq_real, ← mul_div, mul_eq_zero_iff_left] at hx2; norm_cast at hx2
                rw [div_eq_zero_iff, or_comm] at hx2; rcases hx2 with hx2|hx2
                · rw [sq_eq_zero_iff, aux_sin] at hx2; contradiction
                  rw [Set.mem_Icc, ← abs_le]; apply le_of_lt
                  apply lt_trans hx1; apply lt_of_le_of_lt (min_le_right _ _)
                  linarith only [pi_pos]
                push_cast [sq_eq_zero_iff, sin_eq_zero_iff] at hx2
                rcases hx2 with ⟨m, hm⟩; symm at hm
                rw [mul_comm, ← eq_div_iff, div_div_eq_mul_div] at hm
                use m; constructor
                · rw [Int.le_floor, Int.cast_abs]
                  simp only [hm, ← mul_div, abs_mul, abs_div] at hx1
                  norm_cast at hx1; push_cast at hx1
                  nth_rw 2 [abs_eq_self.mpr] at hx1
                  rw [mul_assoc, ← lt_div_iff₀, mul_div, div_div_eq_mul_div] at hx1
                  rw [mul_comm] at hx1; nth_rw 2 [mul_comm] at hx1
                  exact le_of_lt hx1; all_goals positivity
                rw [hm]; ring; positivity
                · simp only [one_div, ne_eq, inv_eq_zero]
                  norm_cast
                revert this; contrapose!
                rw [aux_sin]; exact fun a => a
                · rw [Set.mem_Icc, ← abs_le]; apply le_of_lt
                  apply lt_trans hx1; apply lt_of_le_of_lt (min_le_right _ _)
                  linarith only [pi_pos]
              apply measure_mono at aux_sbst; rw [eq_iff_le_not_lt]; constructor
              · convert aux_sbst; symm; rw [Set.image_eq_iUnion]
                apply measure_iUnion_null
                simp only [Set.mem_setOf_eq, measure_iUnion_null_iff, measure_singleton, implies_true]
              push_neg; exact zero_le'
              exact Measure.instOuterMeasureClass
          · rw [EventuallyLE]; apply ae_restrict_of_forall_mem measurableSet_Ioo
            intro y hy; simp only [Pi.zero_apply, ← mul_sub]
            rw [Set.mem_Ioo, ← abs_lt] at hy
            apply mul_nonneg; positivity
            · rw [sub_nonneg]; apply le_of_lt
              apply hδ; rw [(AddCircle.norm_coe_eq_abs_iff (2 * π) (by positivity)).mpr]
              apply lt_of_lt_of_le hy; apply min_le_left
              · nth_rw 2 [abs_eq_self.mpr]; norm_num
                apply le_of_lt; apply lt_trans hy
                apply lt_of_le_of_lt (min_le_right _ _)
                linarith only [pi_pos]; positivity
          · simp only [← mul_sub]; rw [← integrableOn_Icc_iff_integrableOn_Ioo]
            apply IntegrableOn.continuousOn_mul
            · apply Continuous.continuousOn; apply Continuous.norm
              exact (contDiff_fejerKernel n).continuous
            · rw [IntegrableOn]; apply Integrable.sub
              · apply integrable_const
              rw [← IntegrableOn]; apply aux.mono
              simp only [Set.subset_def, Set.mem_Icc, ← abs_le]
              intro x hx; ring_nf; apply Set.mem_Ioc_of_Ioo
              rw [Set.mem_Ioo, ← abs_lt]; apply lt_of_le_of_lt hx
              apply lt_of_le_of_lt (min_le_right _ _)
              linarith only [pi_pos]; rfl
            exact isCompact_Icc
          · apply Integrable.mul_const; apply Integrable.norm
            rw [← IntegrableOn, ← integrableOn_Icc_iff_integrableOn_Ioo]
            apply Continuous.integrableOn_Icc
            exact (contDiff_fejerKernel n).continuous
          · rw [← IntegrableOn, ← integrableOn_Icc_iff_integrableOn_Ioo]
            apply IntegrableOn.continuousOn_mul
            · apply Continuous.continuousOn; apply Continuous.norm
              exact (contDiff_fejerKernel n).continuous
            · apply aux.mono; simp only [Set.subset_def, Set.mem_Icc, ← abs_le]
              intro x hx; ring_nf; apply Set.mem_Ioc_of_Ioo
              rw [Set.mem_Ioo, ← abs_lt]; apply lt_of_le_of_lt hx
              apply lt_of_le_of_lt (min_le_right _ _)
              linarith only [pi_pos]; rfl
            exact isCompact_Icc
        _ ≤ ∫ (x : ℝ) in (-π)..π, ‖fejerKernel n x‖ * (ε / (4 * π)) := by
          rw [intervalIntegral]; nth_rw 2 [Set.Ioc_eq_empty]
          simp only [Measure.restrict_empty, integral_zero_measure, sub_zero]
          apply setIntegral_mono_set
          · rw [← integrableOn_Icc_iff_integrableOn_Ioc]
            apply Continuous.integrableOn_Icc; apply Continuous.mul
            apply Continuous.norm; exact (contDiff_fejerKernel n).continuous
            exact continuous_const
          · rw [EventuallyLE]; apply ae_of_all
            intro; rw [Pi.zero_apply]; positivity
          · rw [ae_le_set]
            suffices : (Set.Ioo (-min δ (π / 2)) (min δ (π / 2)) \ Set.Ioc (-π) π) = ∅
            · simp [this]
            rw [Set.diff_eq_empty, Set.subset_def]; intro x hx
            apply Set.mem_Ioc_of_Ioo; rw [Set.mem_Ioo, ← abs_lt] at *
            apply lt_trans hx; apply lt_of_le_of_lt (min_le_right _ _)
            linarith only [pi_pos]
          linarith only [pi_pos]
        _ = _ := by
          rw [intervalIntegral.integral_mul_const, integral_norm_fejerKernel]
          field_simp; ring
      apply Set.disjoint_sdiff_left; exact measurableSet_Ioo
      · apply IntegrableOn.continuousOn_mul
        · apply Continuous.continuousOn; apply Continuous.norm
          exact (contDiff_fejerKernel n).continuous
        · rw [← integrableOn_Icc_iff_integrableOn_Ioc, show -π + 2 * π = π by ring] at aux
          apply aux.mono; apply Set.diff_subset; rfl
        rw [← S_eq]; exact S_cpt
      · rw [← integrableOn_Icc_iff_integrableOn_Ioo]
        apply IntegrableOn.continuousOn_mul
        · apply Continuous.continuousOn; apply Continuous.norm
          exact (contDiff_fejerKernel n).continuous
        · apply aux.mono; simp only [Set.subset_def, Set.mem_Icc, ← abs_le]
          intro x hx; apply Set.mem_Ioc_of_Ioo
          ring_nf; rw [Set.mem_Ioo, ← abs_lt]; apply lt_of_le_of_lt hx
          apply lt_of_le_of_lt (min_le_right _ _)
          linarith only [pi_pos]; rfl
        exact isCompact_Icc
