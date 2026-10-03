# 已证明定理速查（THEOREMS.md）

`lean_formalization/` 里**结论性**定理的一行式索引：每条只讲「它证明了什么」，不展开证明。
全部机器验证，Std-only（无 Mathlib）、无 `sorry`、无新公理，`cd lean_formalization && lake build` 全绿。

**收录口径**（全库 866 条 `theorem`，本文收录 ~140 条核心结论）：

- **收录**：`Check.lean` 的 headline 接口 + 各阶段的核心结论（README 的 §15 十一条定理、Phase E/H 结果、boundary ≤7、M4 收缩与误差预算、`ROSA_Credit_New_Results` §1–§5）。
- **不收录**：`def`／结构体／字段投影、`mem_*` 成员关系接口、`*_length` 计数元数据，以及只在别的证明里当工具用的纯算术引理（如 `CreditCandidateCount.sum_map_le_card_mul`、`Route.Valid` 构造子、`Repair.leftCtx`）。
- 定理名前缀是 **namespace**，与文件名偶有不同（如 `AffineEnvelope.lean` → `AffEnv`），各节标题已标注。

---

## 1. 基础层：Route 优先级代数、Cut 算术、LCSuffix

### `Route.lean`（namespace `Route`）
- `rle_total` — ROSA 优先级 `rle` 是全序：任意两条 route 都能比较，故 winner 唯一。
- `rle_antisymm` — `rle` 反对称，故 `rmax` 的取值不依赖选择顺序。
- `rle_rmax_lub` — `rmax a b` 恰是 `a`、`b` 的最小上界（join），后续所有 `max` 分解的基础。
- `rmax_assoc` — `rmax` 结合，故多候选折叠与括号方式无关。
- `rmaxList_lub` — 列表 fold `rmaxList` 仍是全表的最小上界。
- `rmaxList_append` — `rmaxList` 对 `++` 同态，故分块归约再合并等于整体归约。

### `CutArith.lean`（namespace `CutArith`）
- `hook_split` — §4.2 hook 分解的逐点恒等式：`e > s` 时 `min(ℓ_e, e-s)` 按 `δ_e` 取 `e-s` 或 `ℓ_e`。

### `Lcs.lean`（namespace `Lcs`）
- `lcsLen_spec` — `lcsLen q k t e` 确实等于后缀匹配长度，即满足 `SuffixEq`。
- `lcsLen_greatest` — 任何满足 `SuffixEq` 的长度都不超过 `lcsLen`，故它是**最大**后缀匹配。
- `lcsLen_eq_of` — 主刻画：`SuffixEq c` 且 `¬SuffixEq (c+1)` ⟺ `lcsLen = c`（值级接口）。

## 2. K-Cut / Hook-Envelope 与 Q-Cut（§4–§5）

### `HookCut.lean`
- `kcut_hook_decomposition` — §4.3 **Hook-Envelope**：`bruteKCut = max{A(s), P(s), R(s)}`，逐点 brute 最大值精确等于三段 hook 分解。

### `QCut.lean`
- `qcut_future` — owner 在未来（`t < u`）时 Q-cut 不受约束，`bruteQCut = baseRoute`（修掉了 cap 变负的规格 bug）。
- `qcut_length_and_latest_endpoint` — `u ≤ t` 时闭式 `qcutClosed`：长度 `min L_base (t-u)`，端点取最新达阈的 `e`。

## 3. Run-Rectangle、RSP 与 run capacity（§6–§7）

### `RunRectangle.lean`（namespace `RunRect`）
- `run_rectangle_symbol_ne` — 两 run 符号不同 ⇒ 矩形内 `lcsLen = 0`。
- `run_rectangle_offset_lt` — 同符号且 Q 偏移小 ⇒ `lcsLen = x = t-a+1`。
- `run_rectangle_offset_gt` — 同符号且 K 偏移小 ⇒ `lcsLen = y = e-c+1`。
- `run_rectangle_offset_eq` — 同符号且偏移相等 ⇒ `lcsLen = x + lcsLen (a-1) (c-1)`（递归到对角前驱）。
- `run_rectangle_rsp` — 上述四支统一成 ramp/spike/plateau 三分式。
- `run_grid_gamma_recurrence` — §15 #5：run 网格 γ 递推，末点 `lcsLen` 按符号与 min/加法三分。

### `RunRectangleLcp.lean`（namespace `RunRectLcp`）
- `repair_edge_right_rsp` — §15 #11：前向 `lcpLen` 对 `(X=b-p, Y=d-u)` 呈 ramp/spike/plateau。

### `RunRectangleInitial.lean`（namespace `RunRectInitial`）
- `run_rectangle_offset_eq_leftCtx` — 去掉正性前提的等偏移公式，前驱用 `Repair.leftCtx` 守卫。
- `run_rectangle_rsp_leftCtx` — 无正性前提的矩形 RSP 三分式。
- `run_grid_gamma_recurrence_leftCtx` — 无正性前提的 run 网格 γ 递推（覆盖首行/首列基例）。

### `Capacity.lean`（namespace `Capacity`）
- `run_capacity_reaches` — 刻画矩形内哪些端点 `e` 使 `λ ≤ lcsLen`（三支）。
- `run_capacity_latest_endpoint` — §15 #6：给出达阈的**最大**端点：末点 `d`、spike 端点 `c+x-1`，或无。

### `CapacityComplete.lean`（namespace `Capacity`）
- `run_capacity_maxEndpoint?_correct` — `maxEndpoint?` 语义正确：`some e` 即最大可达端点，`none` 即无端点达标。
- `run_capacity_argmax_exists_iff` — 存在达标端点 ⟺ `maxEndpoint? ≠ none`。
- `run_capacity_maxEndpoint?_eq_some_iff` — `= some e` 的精确分支条件（普通端点 `d` 或 spike 端点）。
- `run_capacity_two_records_sufficient` — 同符号矩形内 ordinary/spike **两条**记录即构成精确 max 包络。
- `ordinaryRecord_wins_tie` — 容量相等时取 ordinary 记录（端点 `d`）。

### `CapacityMultiRun.lean`
- `latestAt_is_pointwise_max` — `latestAt` 是达标端点的上界，且存在达标记录时取到。
- `globalRoute_eq_winnerRoute` — 全局 `rmaxList` 路线等于「容量优先、端点次之」的 winnerRoute。
- `qcutClosed_eq_thresholdRoute_of_complete` — 记录集完备时 `qcutClosed` 等于阈值查询 `thresholdRoute`。
- `multiRunRecords_eq_per_run` — 多 run 记录展平 = 各 run 两条记录的 `rmaxList`。

### `CapacityConcrete.lean`
- `multiCapacityRecords_rmax_eq_multiEndpointRecords` — 压缩的 ordinary/spike 记录与逐端点精确记录给出同一条路线。
- `qcutClosed_eq_thresholdRoute_multiCapacityRecords_of_rowCovered` — 行被覆盖时，压缩容量记录直接算出 `qcutClosed`。

### `CapacityRunDecomposition.lean`
- `RunCover.qcutClosed_eq_thresholdRoute_multiCapacityRecords` — 由 sound/complete 的 RunCover 推出压缩容量记录的 Q-cut 桥。
- `RunDecomposition.complete_exact` — 每个因果端点恰属于唯一一个 run 区间。

### `CapacityAutomaticRunCover.lean`
- `automaticCompleteAt` — `t ≤ Tk` 时自动构造的端点记录集对稠密行完备。
- `automaticCapacityRecords_qcut` — 自动混合压缩记录算出 `qcutClosed`（异符号处用零记录）。

## 4. Repair 边界支持与 RSP 形状（§9）

### `Repair.lean`
- `repair_right_boundary_support` — §15 #8：非平凡右上下文（`lcpLen > 0`）只出现在 Q 右端或 K 右端（`p=b ∨ u=d`）。
- `repair_left_boundary_support` — §15 #7：非平凡左上下文（`lcsLen > 0`）只在 `p=a ∨ u=c`。
- `repair_strict_interior_trivial` — §15 #9：`α≠β` 矩形严格内部左右上下文全为 0。
- `repair_edge_left_rsp` — §15 #10：左边界上下文 `L(bp, u-1)` 对 K 偏移呈 RSP 形状。
- `run_grid_gamma_base` — 初始 run（`a=0 ∨ c=0`）时 `leftCtx` 取 0，补上递推的基例缺口。

### `RspSummary.lean`
- `left_edge_context_rsp` — 左边界上下文 `u ↦ L(a,u)` 确为 K 偏移上的 RSP 形状（抽象形状的第一个真实实例）。

> `RspShape.value` / `.threshold` / `.le` 是 RSP 抽象结构的字段投影（API），按口径未单列。

## 5. Phase E：run-compressed K-Hook 摘要（§8）

### `RunHookSummary.lean`（namespace `RunHook`）
- `delta_ramp` — ramp 段内 `δ_e` 恒等于 `c-1`。
- `delta_spike` — spike 点处 `δ_e = c-1-γ`。
- `delta_plateau` — plateau 段 `δ_e = e-x`，随端点线性增长（单位斜率）。
- `P_run_eq` — E1：逐 run 的 `P(s)` 只需 ramp/spike/plateau 三条记录，等价全量 brute。
- `U_plateau_max` — E2：plateau 上 `δ ≤ s` 的最晚端点正是 `min d (s+x)`。
- `A_run_eq` — E3：逐 run 前缀 winner `aComp` = max(末端点, spike)，即「本 run 局部前缀 winner + 全局 carry」。

### `HookDegenerate.lean`（namespace `RunHook`）
- `P_run_eq_all` — 去掉 `2≤x`、`c+x≤d` 的全情形 P 摘要（空阶段自动略去/截断）。
- `U_plateau_max_all` — 全情形 plateau 判据逐点成立，仅在 plateau 非空时给最晚端点见证。
- `A_run_eq_all` — 全情形 A 摘要，`2≤x` 弱化为 `1≤x`（含初始 run）。

### `HookScan.lean`
- `scanCut_eq_hookCut` — dense A/P/U 三扫描合成 = `HookCut.hookCut`。
- `scanCut_eq_bruteKCut` — 该 dense 扫描 = `CutArith.bruteKCut`。
- `delta_neg_one_classification` — `δ = -1` 的端点恒落在 U 侧、从不落入 P 侧。

### `RunHookCoverage.lean`
- `fold_pCompAll_eq_pScan` — 折叠各 run 的 P 摘要 = 全局 `HookScan.pScan`。
- `fold_uCompAll_eq_uScan` — 折叠各 run 的 U 端点最大值 = 全局 `uScan`。
- `fold_aComp_eq_aScan` — 折叠各 run 的 A 摘要 = 全局 `aScan`。
- `foldedHookCut_of_orderedCoverage` — 有序覆盖下折叠 A/P/U 恰好得到 `hookCut`。

### `RunHookCompressedScan.lean`
- `U_run_eq_dense` — K run 内压缩 U 三记录的最大值 = dense 窗口端点最大值。
- `P_run_eq_dense` — 压缩 P 摘要 = dense P 窗口的 `rmaxList`。
- `A_run_eq_dense` — 压缩 A 摘要 = dense A 窗口的 `rmaxList`。
- `foldedRunSummaries_eq_bruteKCut` — 折叠逐 run 摘要组装后 = `bruteKCut`（压缩扫描正确性总装）。

## 6. Phase H：仿射 Route 包络（§11，ROSA 无关核心）

### `AffineEnvelope.lean`（namespace `AffEnv`）
- `wins_convex` — 两条仿射 route 按 `(len,endpoint)` 字典序比出的胜者集是**区间**。
- `wins_interval` — 限定在 `[lo,hi]` 上结论仍成立。
- `wins_list_convex` — 一条 route 在有限模板列表中夺冠的集合仍是区间。

### `OwnerEnvelope.lean`（namespace `OwnerEnv`）
- `envWins_interval` — 有限模板列表下，某 route 为全体 argmax 的集合是区间。
- `two_winner_interval` — 两条仿射 route 中 `g` 胜过 `f` 只出现在单一区间。
- `glue_A_leftToRight` — A 方向（左→右 carry）拼接后夺冠 ⟺ 两段各自夺冠。
- `glue_P_threshold` — P 方向阈值记录：先筛后拼 ⟺ 两段各自筛选再拼。
- `glue_U_union` — U 方向 plateau 并集在任何子列表选择下保持夺冠谓词。
- `glue_interval` — 两段候选拼接后的 owner 包络仍是区间。
- `runPairCands_interval` — 单个 run pair 的桥候选集合，其 owner 包络是区间。
- `runPairTemplates_length` — run pair 折叠模板数 ≤ 9，即每对 `O(1)` 个。
- `runPairTemplates_interval` — 折叠到 run-pair 模板后包络仍区间。
- `interior_same_birth` — 两个严格内部中心的出生值都是 `(1,u)`，内部 bulk 缩成一个模板。
- `row_interval` — 整行各 run 拼接后 owner 包络仍是区间（≤ 9·R_K 段）。
- `interior_bridge_value` — 严格内部中心在 `t=p` 的桥 route 恒为 `(1,u)`。
- `active_not_interval` — **反例**：一旦加入活动区间（birth/death），夺冠集可以不再是区间。

### `OwnerTemplateEquivalence.lean`
- `runPairTemplates_corrected_max_eq_actual` — 修正后的固定 owner 模板 field 逐点等于真实 bridge field（补上审查指出的「9 个任意 route」缺口）。
- `qOwnerTemplates_length_le_three` — Q-owner 严格内部时模板数 ≤ 3。
- `kOwnerTemplates_length_le_three` — K-owner 严格内部时模板数 ≤ 3。

### `Gluing.lean`
- `field_append` — 两候选列表拼接后 field = 两块 field 的 `rmax`。
- `fieldBridges_append` — bridge 列表拼接同样如此，且无附加前提。
- `field_flatten` — 多块 flatten 后 field = 各块 field 的 `rmaxList`。
- `glue_two` — 两块各自 field 与实际块相等 ⇒ 拼接后仍相等（step 12a 二元形式）。
- `glue_pairs` — 每对压缩/实际块 field 相等 ⇒ 多 run flatten 后整体 field 相等。

### `Interior.lean`
- `interior_bridge_route` — 内部桥只在 `t=p` 活动，route 为 `(1,u)`，death = `p`。
- `k_interior_bulk_equiv` — 固定 K-owner `u` 时，内部中心出生 `p` 恰好覆盖 `[max(a+1,u+1), b-1]`。
- `q_interior_bulk_max` — 固定 Q-owner `p` 时，内部 K-endpoint 均 `≤ min(d-1, p-1)`。

## 7. Bridge 语义链与候选寿命

### `RosBridge.lean`
- `bridge_kappa_const` — 桥在活动期内归一化优先级 `κ` 恒定，故优先级与时间无关。
- `route_better_iff_kappa` — 同时活动的两桥，route 序比较 ⟺ `κ` 字典序比较。

### `QBridge.lean`
- `q_bridge_beats_cut` — 活跃的 Q-bridge 其 route 严格胜过 Q-cut 基线（与行 `ell` 无关）。

### `CommonBirth.lean`
- `common_birth_winner_iff` — 共出生候选 `b` 的胜者集恰为 `[max(p, M_b+1), e_b]`。

### `AffineLifetime.lean`
- `winner_change_forces_event` — 相邻时刻 winner 集改变 ⇒ `t+1` 必属有限临界事件表。
- `criticalEvents_length_eq` — 临界事件表长度 = 每候选 2 事件 + 所有成对穿越窗口之和。
- `critical_scan_winner_iff` — 段内无临界事件时，`t` 处 winner 等于段起点 `lo` 处。
- `lifetime_winner_reentry` — **反例**：带 birth/death 时 winner 可以再入（0、10 胜而 5 不胜）。
- `two_candidate_winner_iff` — 两候选下 winner ⟺ 自身活动且（对方不活动或走线更优）。
- `ofBridge_wins_iff_route_rle` — 仿射 winner 关系与 ROSA `Route.rle` 在同活动时刻一致。
- `essentialEvents_nodup` — 去重后的事件表无重复（定义在 `EnvelopeEssentialEvents.lean`）。
- `essentialEvents_length_le` — 去重事件表长度 `≤ 2n + n(n-1)`，`n` 为候选数（同上文件）。
- `essential_scan_winner_iff` — 用去重事件表时，段起点 winner 等于 `t` 处 winner（同上文件）。

> `EnvelopeEssentialEvents.lean` 只提供上面三条 `essential*` 定理（namespace 同为 `AffineLifetime`）：`criticalEvents` 的去重与长度界。

### `EnvelopeExecutable.lean`
- `scanEssential_exact` — 事件扫描器每个输出段满足 `SegmentExact`，段内 winner 精确。
- `scanEssential_covers` — 输出段覆盖 `[lo,hi]` 内每个整数时刻。
- `scanEssential_change_mem_boundaries` — 每次 winner 变化都出现在扫描用的边界列表中。

### `BridgeEnvelope.lean`
- `qOwnerCandidates_winner_iff_bridgeWins` — Q-owner 候选上的 lifetime 包络 winner ⟺ `qOwnerBridges` 上的活跃 raw route 最大者（桥语义与包络层精确对接）。
- `kOwnerCandidates_rawWinner_iff_bridgeWins` — K-owner 的 **raw** 桥包络同构（明确不含删除基线）。
- `rosaKBaselineWinner_label_eq_some_iff` — 带删除基线的 K winner 规范标签 `= some κ` ⟺ 存在活跃桥使 `RosaKBaselineWinner` 且 `b.kappa = κ`。

## 8. K-deletion 基线、区间性与 no-reentry 计数

### `KDeleteAbstract.lean`
- `trim_kappa` — trim 路线后 `κ` 不变，时间整体前移一格。
- `kdelete_step` — `t+1` 时某候选胜过活动桥 `b` ⇒ 其 trim 在 `t` 时仍胜过 `b`。
- `beats_delete_monotone` — `b` 一旦胜过删除基线，在活动期内持续胜过。
- `better_future_bridge_blocks_before_birth` — 更优桥 `c` 未出生前，删除基线已凭 `κ_c` 压过 `b`。
- `shadow_not_beats` — 存在 pre-birth shadow 时 `b` 严格不胜删除基线。

### `KSkyline.lean`
- `k_suffix_winner_iff` — `b` 恰在 `t ∈ [max(p,d,M+1), e_b]` 上是该 owner 的 K-side winner。

### `KDeleteROSA.lean`
- `rosa_trim_closed` — 删除候选裁去末字符后仍是删除候选，故 `TrimClosed` 成立（消解抽象前提一）。
- `rosa_has_prebirth_shadow` — 桥的 `κ_c` 在 `c` 出生前已出现在删除候选中（消解抽象前提二）。
- `rosa_k_suffix_winner_iff` — 两条前提消解后，K-suffix winner 仍恰为该区间（抽象→字符串层落地）。
- `singleton_zero_not_mem_rosaCand` — 修正边界：删除 `k[0]` 时 `[0,0]` 单字符匹配不再算候选。
- `self_endpoint_not_mem_rosaCand` — 候选端点必 `< t`，当前查询端点绝不出现在候选中。

### `KDeleteEquivalence.lean`
- `rosaKDelete_best_eq_hookCut` — 删除候选的最优路线**无条件**等于 `hookCut`。
- `rosaKDelete_beats_iff_bruteKCut_rle` — `b` 胜过删除基线 ⟺ `bruteKCut ≤ b.routeAt t`。

### `KSuffix.lean`
- `k_suffix_ceiling` — 桥自 `d` 起持续 beats 基线 ⇒ 它恰在 `[max(p,d,M+1), e]` 上成为最终 K 侧 winner。

### `BlockWinnerNoReentry.lean`
- `qKeyWins_isInterval` — 固定 Q-owner 下每个 `κ` 身份类的 winner 集是闭区间。
- `kKeyWins_isInterval` — 固定 K-owner 下同理（需各桥局部区间）。
- `segments_le_three_mul_of_isInterval_on` — 只要求实际出现的标签具区间性，winner 段数即 `≤ 3m`。
- `crossBlock_canonical_reentry` — **反例**：跨块规范标签序列 weak/strong/weak 确实再入。

### `Phase12b.lean`
- `segments_le_of_subset` — 无再入序列的极大常量段数不超过其标签全集大小。
- `flatten_length_le` — 每块 ≤3 候选时 flatten 后总数 `≤ 3m`。
- `segments_le_three_mul` — 每块 ≤3 + winner 无再入 + 标签取自候选 ⇒ 段数 `≤ 3m`。
- `segStart_label_ne` — 每标签 winner 集是区间 ⇒ 两不同段起点标签必不同（即无再入）。
- `segStarts_le_of_subset` — 区间 winner 集下，段起点数不超过标签表大小。
- `segments_le_three_mul_of_isInterval` — 每块 ≤3 且每标签 winner 集为区间 ⇒ 段数 `≤ 3m`。
- `qCBCand_isInterval` — common-birth 候选的 winner 集是区间（Q 侧）。
- `kSuffixWinner_isInterval` — K-side suffix winner（含删除基线）的 winner 集是区间。
- `bridge_route_eq_routeOfKappa` — 活动桥的 `routeAt` 等于以其 `κ` 参数化的仿射路线。
- `bridge_route_affine` — 桥走线斜率恒为 `(1,1)`：len、endpoint 都是 `t` 加常数。
- `routeOfKappa_inj` — `routeOfKappa` 单射：不同 `κ` 给出不同仿射路线。
- `bridge_affineOn` — 桥在整段生命期内都是一条仿射片段。
- `overlay_breakpoints_le` — 基座 q 段被 `r` 个修复区间覆盖后，总段数 `≤ q + 2r`。

### `OwnerBridges.lean`
- `qOwnerBridges_birth` — `qOwnerBridges` 中每个桥的出生时刻都是固定 Q-owner `p`。

> `OwnerCompress.lean` 在 `Check.lean` 中只有压缩候选的定义与 `mem_*` 接口（`Cand`、`candOf`、`field`、`qOwnerCompressed`…），其**正确性**见下一节。

## 9. 固定 owner 的压缩正确性与 O(1) 候选

### `OwnerCorrect.lean`
- `mkBridge_strict_interior` — 严格 interior 桥满足 `R = 0`，只在出生点 `p` 活跃并贡献 `(1,u)`。
- `qOwnerCompressed_field` — Q 侧压缩列表与原 `fieldBridges` 对每个 `t` 逐点相等（step 11-Q 精确性）。

### `OwnerCorrectK.lean`
- `bval_dropped` — 被丢弃的 K-owner 桥只在出生 `p` 活跃，取值 `(1,u)`。
- `bulkRoute_le_field` — `bulkRoute` 被实际桥字段逐点支配。
- `kOwnerCompressed_field` — K 侧压缩列表与原字段逐点相等（step 11-K 精确性）。

### `WinnerPieces.lean`
- `qOwnerCompressed_length_le_three` — 严格 interior Q-owner 的压缩列表长度 ≤ 3。
- `kOwnerCompressed_length_le_three` — 严格 interior K-owner 的压缩列表长度 ≤ 3。
- `qOwner_filter_subset` — 活跃 kept Q-center 必是 `c`、`d`、`u_*` 三个 slot 之一。
- `kOwner_filter_subset` — 活跃 kept K-center 必是 `a`、`b` 两个 edge slot 之一。
- `qOwner_field_three` — Q winner field = 三个 slot 贡献的 `rmax`（O(1) 个候选即足够）。
- `kEdge_rmax_eq` — 两个 K edge slot 的 `rmax` 等于全部 kept center 的 field。
- `kOwner_field_three` — K winner field = `bulkRoute` 与两个 edge slot 的 `rmax`。

### `OwnerKBaselineEnvelope.lean`
- `fixedKOwner_effectiveWinner_isInterval_of_window` — 有 ROSA window 时固定 owner winner 取值集是 interval（无 re-entry）。
- `kOwner_segments_le_three_mul_of_uniform` — 单 owner、各块 ≤3 ⇒ canonical winner 段数 `≤ 3·块数`。

### `OwnerKWindowDischarge.lean`
- `hasRosaKWindow_of_mem_kOwnerBridges` — 桥属于 `kOwnerBridges` 且有单点删除锚点 ⇒ 得到 `HasRosaKWindow`。
- `fixedKOwner_canonicalWinner_isInterval_of_kOwnerBridges` — 每座桥各有删除锚点 ⇒ canonical winner 恒等类是 interval。

### `EffectiveOwnerM3.lean`
- `qEffectiveRoute_repair_or_cut` — Q effective route 必等于 repair 字段或 Q cut 之一。
- `kEffectiveRoute_eq_rmax_rosa_best_raw` — K effective route = `rmax(rosaKDelete.best, rawKOwnerField)`。
- `kEffectiveRoute_eq_threeField_of_strict` — 严格 interior 时 = `rmax(rosa best, 三 slot 字段)`。
- `q_and_k_effective_routes_are_owner_scoped` — Q、K 的 repair 列表各只含本 owner 的桥，不跨 owner 竞争。

## 10. 边界证书：有效割槽 ≤ 7

### `BoundaryPartition.lean`
- `rectPoint_strictInterior_or_onEdge` — 闭矩形内任一点要么严格内部，要么落在四条命名边之一。
- `positive_context_edge_cover` — 左/右 guarded context 任一为正 ⇒ 中心必在四条边之一。
- `context_edge_cover_or_strictInterior_zero` — 错配矩形的内点二分：或在四边之一，或严格内部且两个 context 均为零。
- `edgeMembershipCount_le_four` — 一个点至多同时属于 4 个不同边标签。
- `all_four_edges_of_singleton` — 宽高皆为 1 的退化矩形会同时命中全部四条边。

### `BoundaryRangeCount.lean`
- `boundary_range_count_le_seven` — 四条 edge record 裁剪后的八个割位至多产生 **7** 个有效 range。
- `boundary_rsp_certificate_range_count_le_seven` — 输入换成字符串级 RSP 证书，同样 `≤ 7`。

### `BoundaryZeroCertificates.lean`
- `BoundaryRunsComplete.certificate_range_count_le_seven` — 六 run 全覆盖窗口（含符号不匹配全情形）有效割仍 ≤ 7。

### `BoundaryCertificates.lean`
- `StringBoundaryRuns.certificate_range_count_le_seven` — 给定具体六 run 字符串证书，边界编译器有效割数 ≤ 7。

### `BoundaryOptionalWindow.lean`
- `Window.certificate_range_count_le_seven` — 允许前后 run 缺失的可选窗口，装配证书后 range count 仍 ≤ 7。
- `Window.exists_window_of_fullRunList_mem` — `fullRunList` 中任意错配 run 对都能构造出这样的可选窗口。

### `BoundaryRecursive.lean`
- `completeToDirect_range_count_le_seven` — 六 run complete 证书经 direct 装配接口后，同一有效割仍 ≤ 7。

### `BoundaryRunExtractor.lean`
- `rightCertificateOfStringRun` — `fullRunList` 中任一 Q run 对固定 K run 都存在右边界 RSP 证书。
- `topCertificateOfStringRun` — 任一 K run 对固定 Q run 都存在上边界 RSP 证书。
- `BoundaryWindow.certificate_range_count_le_seven` — 六 run 边界窗口直接装配四边证书后 range count ≤ 7。

## 11. M4 payload：收缩恒等式与误差预算

### `PayloadContraction.lean`
- `intervalDot_eq_prefix_sub` — 区间 payload 点积 = 乘积序列的 exclusive prefix 差。
- `constantEndpointContraction_eq_contraction` — 常量端点 contraction 等价于以常量作候选的 pointwise contraction。
- `endpointShiftContraction_eq_contraction` — endpoint-shift contraction = 按索引 `t+(s+1)` 读 payload 的 pointwise contraction。
- `winnerIntervals_accum_eq_pointwise` — winner 区间链上累加的点积和 = 覆盖区间的整体点积。

### `PayloadRouteAdapter.lean`
- `bridgeAffinePiece_shiftedEndpoint` — Bridge 整个 lifetime 是端点形如 `t+shift` 的仿射 piece，`shift = -κ₂-1`。
- `constantEndpointWinnerChain_eq_pointwise` — 常量端点 winner 链上累加 = 覆盖区间上的精确 pointwise contraction。
- `endpointShiftWinnerChain_eq_pointwiseSum` — 端点平移 winner 链每段换成精确 pointwise 后累加，结果不变。

### `PayloadErrorBound.lean`
- `approxContraction_close` — base/candidate 逐点近似精确 payload ⇒ 近似 contraction 在预算内接近精确值。
- `chain_contraction_close` — 全局逐点误差下，近似 contraction 沿 winner 链累加仍接近整体精确值。
- `chain_constantEndpointContraction_close` — 常量端点情形的链式误差界。
- `chain_endpointShiftContraction_close` — 端点平移情形的链式误差界。
- `chain_contraction_exact` — 零舍入预算且值精确时，链式近似退化为精确值。

## 12. `ROSA_Credit_New_Results` 包（§1–§5）

### `CreditRepairReduce.lean` — §1：严格内部 Q-owner 由三候选降为两候选
- `right_ctx_zero_of_not_right_end` — 不取 K-run 右端时桥的右 context 必为 0（右 Boundary-Support 的逆否）。
- `carry_forces_k_right_end` — `R > 0` ⇒ 桥落在 K-run 右端，即 `u = d`。
- `qOwnerBridges_carry_unique` — 三个代表中心中，仅 K 右端那个能活过出生时刻 `p`。
- `two_candidates_reproduce_envelope` — 保留「出生最优 + 唯一存活」两个候选，即可在 `t ≥ p` 重现整个 repair 包络。

### `CreditCandidateCount.lean` — §2：候选总量 `C ≤ T(5·R_Q+4·R_K)`
- `sum_len_le_of_ordered` — 有序 run 在 `[0,T)` 内覆盖的总长度 ≤ `T`。
- `sum_interior_le_of_ordered` — run 的严格内部位置数之和也 ≤ `T`。
- `strictInterior_keep_le_two` — 每个严格内部 Q-owner 保留 ≤ 2 个候选即重现包络。
- `repair_candidate_bound` — 四类 owner 候选数之和 ≤ `T(5·R_Q+4·R_K)`。
- `repair_candidate_bound'` — 对称弱形式：候选总数 ≤ `5T(R_Q+R_K)`。

### `CreditQEExpiry.lean`（namespace `QEExpiry`）— §3：Q 修复包络 = 优先级排序 + 到期扫描
- `bridge_rle_const` — 同 birth 的两桥在共同存活期内排序不变（优先级与时间无关）。
- `scanAll_covered` — 扫描游标终值为 `max cov (max death)`，故发射段铺满到最晚 expiry。
- `scanAll_length_le` — 每个候选至多发射一段，故段数不超过候选数。
- `qExpirySkyline_spec` — 每段标注的桥在该段各时刻都是存活候选中的 ROSA winner（**正确性**）。
- `qExpirySkyline_covered` — 从 `p-1` 起扫，覆盖上界为 `max(p-1)(maxDeath bs)`。
- `qExpirySkyline_length_le` — expiry skyline 段数不超过候选数（**复杂度**）。

### `CreditBlockConv.lean` — §4：移位内积的分块卷积恒等式与最优块大小
- `convCoeff_eq_blockDot` — 反转块与 V 卷积后第 `s+B-1+δ` 个系数恰等于该块的移位点积。
- `blockDecomposition` — 长度 `n·B` 的区间点积 = 各块卷积系数之和（块前缀之差）。
- `chanConv_eq_chanDot` — D-channel 下卷积系数之和 = 各 channel 点积之和。
- `nBlocks_mul_ge` — `⌈T/B⌉` 个长度 `B` 的块足以覆盖全部 `T` 个位置。
- `nBlocks_le` — 块数 `⌈T/B⌉ ≤ T/B + 1`。
- `balance_div` — `B² = A/M` 时两成本项 `A/B` 与 `M·B` 相等（最优块大小算术）。
- `balance_sum` — 平衡处两成本项之和为 `2·M·B`。

### `CreditCRT.lean` — §5：CRT 恢复唯一性
- `crt_unique` — `2|x|, 2|y| < P` 且 `x ≡ y (mod P)` ⇒ `x = y`。
- `crt_unique_three` — 三模数积 `> 2·H_g` 时 CRT 恢复的有界答案唯一。

---

## 未收录与边界

- **未收录**：`def`／结构体／字段投影（如 `OwnerCompress.qOwnerCompressed`、`Phase12b.compress`、`RspShape.value`）、`mem_*` 接口、纯算术工具引理（`sum_map_le_card_mul`、`CreditCRT.two_natAbs_lt_of_le`、`Repair.leftCtx`、`Route.Valid` 构造子）、以及边界模块里装配证书的 `*_certificate` 定义。
- **Phase H 未作全局闭合**：包络定理都在固定 owner / 有限模板层；`active_not_interval`、`lifetime_winner_reentry`、`crossBlock_canonical_reentry` 是三个显式反例，任何全局 `≤ 3m` 结论都必须额外携带 lifetime 与跨块覆盖假设。
- **渐近界未形式化**：`ROSA_Credit_New_Results` 里 `Õ(DT^{3/2})` 等时间界没有做 Lean 渐近分析；上面 §2/§4/§5 只机器验证了这些界所依赖的**数学内容**（候选计数恒等式、块卷积恒等式与代价平衡、精确恢复条件）。
- **浮点未覆盖**：M4 误差界是整数近似代数（预算式），不主张与任何 `Float32/64` 归约顺序逐位一致；`FloatBudget` 仍 OPEN。
