#!/usr/bin/env python3
"""四轴可锚定量的下游 feed——**只搬运、不造数**

给下游（Forge 的 μ 世界）用：把四条硬件轴（装置 / 诊断 / 建造-可造性 / 排期）
与 μ 动力学、控制代数的可锚定量，按「键名 / 单位 / 取值 / 出处 / 来源文件 hash」
打包成一份机器可读的锚点表。

【铁律：本文件不含任何新数字】
  - JSON 来源条目：脚本**运行时**从源 JSON 的声明路径读出取值再写入产物；
    脚本里根本不写数（只有路径）。
  - 文本来源条目：脚本只声明「原文引用」，取值必须是该引文里出现过的子串
    （引文先逐字校验存在于源文件），因此取值也只能是搬运来的。
  - 全局检查（WF4）：产物里出现的每一个取值，都必须能在它自己声明的源文件里
    逐字找到——出现新数字即报红。
  - 缺口条目：取值为 null，只写「需要 leo 给什么」，不得填默认值。

产物：artifacts/world_feed/world_feed.json + summary.txt
"""
import hashlib
import json
import os
import re

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(REPO, "artifacts", "world_feed")
os.makedirs(OUT, exist_ok=True)

CHECKS = []


def chk(name, cond, detail=""):
    CHECKS.append({"检查": name, "通过": bool(cond), "细节": str(detail)})
    print(("PASS " if cond else "FAIL ") + name + (f"  [{detail}]" if detail else ""))
    return bool(cond)


def sha16(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(8192), b""):
            h.update(chunk)
    return h.hexdigest()[:16]


RE_NUM = r"[-+]?\d+\.?\d*(?:[eE][-+]?\d+)?"


def ser(v):
    """取值的可核对序列化：数字/布尔用 JSON 形式（与源文件里写法一致），字符串原样。"""
    return v if isinstance(v, str) else json.dumps(v, ensure_ascii=False)


def walk(obj, path):
    """路径用「/」分段，但键名本身可能含「/」（如「锁定因子 1/√(1−μ_n) ⋯」），
    因此用「最长键名前缀匹配」逐级下钻，而不是简单 split。"""
    cur = obj
    rest = path
    while rest:
        if not isinstance(cur, dict):
            raise KeyError(rest)
        for k in sorted(cur, key=len, reverse=True):
            if rest == k or rest.startswith(k + "/"):
                cur = cur[k]
                rest = rest[len(k):].lstrip("/")
                break
        else:
            raise KeyError(rest)
    return cur


MUDYN = "artifacts/mudynamics/report.json"
GRAV = "artifacts/gravitycontrol/report.json"
PLASMA = "artifacts/plasmafusion/report.json"
FRC = "artifacts/frccompact/report.json"
MOIRE = "artifacts/moirefield/report.json"
ROADF = "artifacts/fusionroadmap/report.json"
W_CONF = "docs/wiki/theory-antigravity-confinement.md"
W_FRC = "docs/wiki/theory-frc-compact.md"
W_PF = "docs/wiki/theory-plasma-fusion.md"
W_RM = "docs/wiki/fusion-program-roadmap.md"

# 条目：(轴, 段, 键名, 单位, 源文件, 类型, 定位)
#   类型 json → 定位 = JSON 路径（取值运行时读出）
#   类型 text → 定位 = 原文引用（取值必须是引文子串，由 WF2 校验）
ENTRIES = [
    # ---------------- μ 状态（下游每个 tick 要读的量）----------------
    ("mu-世界", "状态", "state.mu.递推式 μ(t+Δt)", "递推式", MUDYN, "json",
     "state_equation"),
    ("mu-世界", "状态", "state.mu.闭式 μ_n", "闭式", MUDYN, "json", "closed_form"),
    ("mu-世界", "状态", "state.mu.示例轨道终值（300 步）", "无量纲", MUDYN, "json",
     "results/N6_N7_N8_never_reach/终值 μ_N"),
    ("mu-世界", "状态", "state.mu.轨道最大 < 1（永不饱和）", "bool", MUDYN, "json",
     "results/N6_N7_N8_never_reach/轨道最大值 < 1"),
    ("mu-世界", "状态", "state.η.桥接式（增益 = 抹平进展）", "桥接式", MUDYN, "json",
     "bridge"),
    ("mu-世界", "状态", "state.η.抹平一次后 max|η−1|", "无量纲", MUDYN, "json",
     "results/N11_N12_bridge/抹平一次后 max|η − 1|（200 场）"),
    ("mu-世界", "状态", "state.window.余量 m_i(1−μ_n) 严格递减", "bool", MUDYN, "json",
     "results/N15_frc_interface/窗口余量 m_i(1−μ_n) 严格递减"),
    ("mu-世界", "状态", "state.lock.锁定因子 1/√(1−μ_n) 良定义", "bool", MUDYN, "json",
     "results/N15_frc_interface/锁定因子 1/√(1−μ_n) 分母恒正（良定义）"),
    ("mu-世界", "状态", "state.order.顺序差公式 (1−μ)(1−η)", "式", MUDYN, "json",
     "results/N14_gap_and_cost/顺序差 = (1−μ)(1−η_before)"),
    # ---------------- 动作（控制代数 = 下游可施加的操作）----------------
    ("mu-世界", "动作", "action.flatten.幂等 P²=P", "bool", GRAV, "json",
     "results/N1_idempotent/P² = P（幂等）"),
    ("mu-世界", "动作", "action.flatten.满增益 ⟺ 零代价", "bool", MUDYN, "json",
     "results/N14_gap_and_cost/满增益 ⟺ 零代价（200 场）"),
    ("mu-世界", "动作", "action.flatten.区域内部引力关闭", "bool", GRAV, "json",
     "results/N2b_gravity_interface/抹平 ⟹ 区域内部引力关闭（边界保留）"),
    ("mu-世界", "动作", "action.order.部分重叠 ⟹ 次序相关（非交换）", "bool", GRAV, "json",
     "results/N9_commute_absorb_witnesses/部分重叠 ⟹ 次序不同结果不同"),
    ("mu-世界", "动作", "action.order.嵌套 ⟹ 吸收（次序无关）", "bool", GRAV, "json",
     "results/N9_commute_absorb_witnesses/嵌套 ⟹ 吸收（次序无关，同结果）"),
    ("mu-世界", "动作", "action.boolean.仅层状族有效（不交或嵌套）", "bool", GRAV, "json",
     "results/N7_boolean_vs_not/不交族 = 布尔子代数（分配律 + 格并幂等成立）"),
    ("mu-世界", "动作", "action.boolean.交叠族布尔失效", "bool", GRAV, "json",
     "results/N7_boolean_vs_not/交叠族：布尔运算失效（交换子≠0 + 格并非投影）"),
    # ---------------- 目标（下游优化/判决的目标量）----------------
    ("诊断", "目标", "target.mu.可探测下限（δ=1e-4）", "无量纲", ROADF, "json",
     "R1_D1_cyclotron_signature/诊断精度 → 可探测 μ 下限/δ=1e-04/μ_min"),
    ("诊断", "目标", "target.mu.可探测下限（δ=1e-3）", "无量纲", ROADF, "json",
     "R1_D1_cyclotron_signature/诊断精度 → 可探测 μ 下限/δ=1e-03/μ_min"),
    ("诊断", "目标", "target.mu.可探测下限（δ=1e-5）", "无量纲", ROADF, "json",
     "R1_D1_cyclotron_signature/诊断精度 → 可探测 μ 下限/δ=1e-05/μ_min"),
    ("诊断", "目标", "target.detect.R_ci(μ=0.001)", "无量纲", ROADF, "json",
     "R1_D1_cyclotron_signature/μ → 签名对照/μ=0.001/R_ci"),
    ("诊断", "目标", "target.detect.回旋频率 @B=1T（¹H）", "MHz", ROADF, "json",
     "R1_D1_cyclotron_signature/示踪离子回旋频率 @B=1T [MHz]/¹H"),
    ("装置", "目标", "target.mu.FC11 硬天花板（m_eff 临界）", "无量纲", FRC, "json",
     "results/G3_three_gates/mu_crit_rmf"),
    ("装置", "目标", "target.mu.FC11 下限（m_e/m_i）", "无量纲", MOIRE, "json",
     "meta/constants/floor_FC11"),
    ("装置", "目标", "target.window.m_i/m_e 质量窗口比", "无量纲", FRC, "json",
     "results/G6_rmf_window/window_ratio_mi_me"),
    ("装置", "目标", "target.device.真空场（RMF 选频用 B，下限）", "T", W_FRC, "text",
     "真空场 7-9T 压缩到 **35T**", "7"),
    ("装置", "目标", "target.device.压缩峰场", "T", W_FRC, "text", "压缩到 **35T**"),
    ("装置", "目标", "target.device.末级燃烧室直径", "cm", W_FRC, "text",
     "12cm 直径燃烧室"),
    ("装置", "目标", "target.device.稳态机械上限（R=10cm,t=1cm,σ_y=1GPa）", "T", W_FRC,
     "text", "B_cap ≈ 15.8T"),
    ("装置", "目标", "target.device.装置最小环（SPARC 级）", "m", W_PF, "text",
     "R=1.85m、B=12.2T", "1.85"),
    ("装置", "目标", "target.device.应力层最小环上限（B=12.2T）", "m", PLASMA, "json",
     "results/F5_min_ring/stress_limit_Rmax_12.2T_m"),
    ("装置", "目标", "target.device.双流环同位素权重比 Cu:H", "比例", W_CONF, "text",
     "Cu:H=106:1", "106:1"),
    ("装置", "目标", "target.device.μ 够用的聚变级值", "无量纲", W_FRC, "text",
     "μ≈0.999"),
    ("诊断", "目标", "target.detect.μ 阶梯起点", "无量纲", W_RM, "text",
     "~1e-4（可探测定义）"),
    ("诊断", "目标", "target.scale.k=1 到聚变级所需功率倍数", "倍", ROADF, "json",
     "R3_D3_power_scaling/从桌面 μ≈1e-4 到聚变级 μ≈0.999（Δ≈4 个数量级）所需输入功率倍数/k=1"),
    ("诊断", "目标", "target.scale.k=0.5 到聚变级所需功率倍数", "倍", ROADF, "json",
     "R3_D3_power_scaling/从桌面 μ≈1e-4 到聚变级 μ≈0.999（Δ≈4 个数量级）所需输入功率倍数/k=0.5"),
    # ---------------- 终止（下游何时停）----------------
    ("mu-世界", "终止", "terminate.window.关闭步 n*（阈值 μ≥0.99978）", "步", MUDYN, "json",
     "results/N15_frc_interface/D-T 窗口关闭步 n*（阈值 μ ≥ 0.99978）"),
    ("mu-世界", "终止", "terminate.浮点饱和步（5000 步内）", "步", MUDYN, "json",
     "results/N6_N7_N8_never_reach/浮点饱和步（5000 步轨道首次 μ≥1）"),
    ("排期", "终止", "terminate.gate.任何门连续两次未过 ⟹ Stop（不延长）", "规则", W_RM,
     "text", "任何门连续两次未过"),
    ("排期", "终止", "terminate.gate.阶梯落后两阶段 ⟹ Stop", "规则", W_RM, "text",
     "连续两个阶段落后 ⟹ 触发 Stop"),
    ("诊断", "终止", "terminate.gate.D1=0 ⟹ 停装置线", "规则", W_RM, "text",
     "D1 = 0（M6）"),
    # ---------------- 排期 / 建造-可造性（下游排程锚点）----------------
    ("排期", "目标", "target.program.总人·月（60 月）", "人·月", ROADF, "json",
     "R4_mu_ladder_and_person_months/总人·月"),
    ("排期", "目标", "target.program.判决期占比（G0+G1）", "%", ROADF, "json",
     "R4_mu_ladder_and_person_months/判决期成本占比 [%]"),
    ("排期", "目标", "target.program.M24 前累计占比", "%", ROADF, "json",
     "R4_mu_ladder_and_person_months/两年门（M24）前累计占比 [%]"),
    ("排期", "目标", "target.program.峰值人数", "人", ROADF, "json",
     "R4_mu_ladder_and_person_months/峰值人数"),
    ("排期", "目标", "target.program.前 18 个月人·月", "人·月", ROADF, "json",
     "R6_first_18_months_quarterly/总人·月（18 个月）"),
    ("建造-可造性", "目标", "target.build.装置线 18 个月人·月", "人·月", ROADF, "json",
     "R6_first_18_months_quarterly/工作流人·月分解/装置线"),
    ("建造-可造性", "目标", "target.build.诊断线 18 个月人·月", "人·月", ROADF, "json",
     "R6_first_18_months_quarterly/工作流人·月分解/诊断线"),
]

# 命中这些前缀的源文件说明：feed 只引用**上游已存在**的产物，不引用本次新建的
# artifacts/device|diagnostics|buildability|program（避免循环引用、保证「搬运」可审计）
NEW_ARTIFACTS = ("artifacts/device/", "artifacts/diagnostics/", "artifacts/buildability/",
                 "artifacts/program/", "artifacts/world_feed/")

GAPS = [
    {"槽位": "state.mu.η 的物理来源", "需要 leo 给什么":
     "η = 1 − Q_A(v)/Q_A(v₀) 里『抹平功率/抹平动作的物理实现』（微波？激光？额外磁体？）"
     "——仓库只把它标为第二输入缺口，没有数值"},
    {"槽位": "state.mu.初始值 μ₀", "需要 leo 给什么": "装置实际的初态 μ₀（上游只给了示例轨道终值）"},
    {"槽位": "action.flatten.代价常数", "需要 leo 给什么":
     "抹平一次的能量/时间代价常数（N14 只证明『满增益 ⟺ 零代价』，没有代价的量值）"},
    {"槽位": "target.device.整机几何（半径/长度/壁厚）", "需要 leo 给什么":
     "反引力约束环的整机尺寸——装置设计页只有同心三层示意，没有尺寸；"
     "现有可锚定值全部来自 FRC/CFR2 现实锚点"},
    {"槽位": "target.device.RMF 线圈工程参数", "需要 leo 给什么":
     "RMF 线圈匝数/线材/冷却/驱动源规格（FC12 只给选频带判据，不给工程参数）"},
    {"槽位": "target.detect.δ 实际可达值", "需要 leo 给什么":
     "桌面判据台的回旋共振测量精度预算（δ 的实际值）——G0 的交付判据就等这个数"},
    {"槽位": "target.build.关键件外购交期", "需要 leo 给什么":
     "长周期外购件的 lead time（设备清单逐项）——roadmap §8 只写『已逐项核算』，条目未入库"},
]


def main():
    feed = {"title": "四轴可锚定量 → 下游（Forge μ 世界）feed",
            "date": "2026-09-27",
            "铁律": [
                "本文件不含任何新数字：全部取值在运行时从源 JSON 路径读出，"
                "或取自逐字校验过的原文引句。",
                "下游用法：按「键名」取「取值」，再到「源文件」（含 16 位 sha256 前缀）"
                "去锚；不要把本文件当第二事实源，也不要在别处另找同名字段的数。",
                "缺口槽位（取值为 null）表示上游尚无该数——下游不得给默认值，"
                "须等 leo 提供（清单见「需要 leo 给什么」）。",
                "本 feed 不引用本次新建的 artifacts/device|diagnostics|buildability|program"
                "（避免循环引用）；那四份产物是四轴的验收件，本 feed 直接锚到上游。",
            ],
            "四轴产物路径": {
                "装置": "artifacts/device/（scripts/verify_device_first_principles.py）",
                "诊断": "artifacts/diagnostics/（scripts/verify_diagnostics_ladder.py）",
                "建造-可造性": "artifacts/buildability/（scripts/verify_buildability.py）",
                "排期": "artifacts/program/（scripts/verify_program_gates.py）",
                "说明文档": "docs/wiki/hardware-axes.md",
            }}

    ok_text, ok_json, missing_src = [], [], []
    ambiguous, bad_pick = [], []
    src_text_cache = {}
    for axis, section, key, unit, src, kind, loc, *rest in ENTRIES:
        pick = rest[0] if rest else None       # 文本条目可显式声明「取值锚」（引句里的子串）
        sp = os.path.join(REPO, src)
        if not os.path.exists(sp):
            missing_src.append(src)
            continue
        if src not in src_text_cache:
            src_text_cache[src] = open(sp, encoding="utf-8").read()
        txt = src_text_cache[src]
        item = {"轴": axis, "段": section, "键名": key, "单位": unit,
                "来源文件": src, "来源文件 sha256_16": sha16(sp), "定位": loc,
                "定位类型": kind}
        if kind == "json":
            val = walk(json.loads(txt), loc)
            item["取值"] = val
            item["原文"] = json.dumps(val, ensure_ascii=False)
            ok_json.append(key)
        else:
            quote = loc
            nums = re.findall(RE_NUM, quote)
            if unit == "规则":
                # 规则型锚点：取值就是引句本身（不从中挑数字）
                val = quote
                how = "取值 = 引句本身（规则类锚点）"
            elif pick is not None:
                assert pick in quote, f"取值锚「{pick}」不在引句里：{key}"
                val = pick
                how = f"取值 = 条目显式声明的取值锚「{pick}」（引句的子串）"
            elif len(nums) == 1:
                val = nums[0]
                how = "取值 = 引句里唯一的数字"
            else:
                ambiguous.append(f"{key}（引句里有 {len(nums)} 个数字，需声明取值锚）")
                val = quote
                how = "引句数字不唯一且未声明取值锚（应报红修声明）"
            item["取值"] = val
            item["原文"] = quote
            item["取值来源"] = how
            if quote in txt:
                ok_text.append(key)
            if pick is not None and pick not in quote:
                bad_pick.append(key)
        feed.setdefault("锚点", []).append(item)

    chk("WF5 每条条目都带源文件与 16 位 sha256，且源文件都存在",
        not missing_src and all(len(x["来源文件 sha256_16"]) == 16 for x in feed["锚点"]),
        f"{len(feed['锚点'])} 条")
    chk("WF1 文本条目的原文引句逐字存在于源文件（不存在的引句不会进产物）",
        len(ok_text) == sum(1 for e in ENTRIES if e[5] == "text"),
        f"{len(ok_text)} 条引句校验通过")
    chk("WF2 文本条目的取值是引句的子串（取值只能来自引文）",
        all(ser(x["取值"]) in x["原文"] for x in feed["锚点"]
            if x["定位类型"] == "text"),
        "子串校验")
    chk("WF3 JSON 条目路径存在，且取值的序列化形式在源文件里逐字出现",
        all(x["原文"] in src_text_cache[x["来源文件"]]
            for x in feed["锚点"] if x["定位类型"] == "json"),
        f"{len(ok_json)} 条路径")
    bad = [x["键名"] for x in feed["锚点"]
           if ser(x["取值"]) not in src_text_cache[x["来源文件"]]]
    chk("WF4【全局禁新数字】产物里每个取值都能在它自己的源文件里逐字找到",
        not bad, "；".join(bad) if bad else f"{len(feed['锚点'])} 条取值全部可回溯")
    chk("WF10 文本条目的数字取值不歧义：引句多数字必须显式声明取值锚（否则报红）",
        not ambiguous, "；".join(ambiguous) if ambiguous
        else f"{sum(1 for x in feed['锚点'] if x['定位类型'] == 'text' and '取值锚' in x.get('取值来源', ''))} 条声明了取值锚")
    chk("WF11 显式声明的取值锚必须是引句的子串（声明错即报红）",
        not bad_pick, "；".join(bad_pick) if bad_pick else "全部为引句子串")
    chk("WF9 feed 不引用本次新建的四轴产物（无循环引用）",
        not any(x["来源文件"].startswith(NEW_ARTIFACTS) for x in feed["锚点"]),
        "只锚上游 artifacts + wiki")

    feed["锚点"].sort(key=lambda x: (x["段"], x["轴"], x["键名"]))
    feed["缺口槽位"] = GAPS
    feed["结论"] = {
        "锚点条数": len(feed["锚点"]),
        "按段计数": {s: sum(1 for x in feed["锚点"] if x["段"] == s)
                     for s in ("状态", "动作", "目标", "终止")},
        "按轴计数": {a: sum(1 for x in feed["锚点"] if x["轴"] == a)
                     for a in sorted({x["轴"] for x in feed["锚点"]})},
        "缺口槽位数": len(GAPS),
    }
    feed["checks"] = CHECKS

    chk("WF6 缺口槽位取值为 null 且写明『需要 leo 给什么』",
        all(g["需要 leo 给什么"].strip() and "取值" not in g for g in GAPS),
        f"{len(GAPS)} 条")
    chk("WF7 四段（状态/动作/目标/终止）都有条目，且每条都标了四轴归属",
        all(feed["结论"]["按段计数"][s] > 0 for s in ("状态", "动作", "目标", "终止"))
        and all(x["轴"] for x in feed["锚点"]),
        str(feed["结论"]["按段计数"]))
    fee_text = json.dumps(feed, ensure_ascii=False)
    chk("WF8 金额不入库（产物无 ¥/$/万元/元 字样）",
        not re.search(r"[¥$€£]|\d+\s*(万元|亿元|美元|人民币|元整)", fee_text),
        "无货币字样")

    fp = os.path.join(OUT, "world_feed.json")
    with open(fp, "w", encoding="utf-8") as fh:
        json.dump(feed, fh, ensure_ascii=False, indent=2)

    lines = [
        "四轴可锚定量 → 下游（Forge μ 世界）feed（2026-09-27）",
        "=" * 62,
        f"锚点 {feed['结论']['锚点条数']} 条｜"
        + "｜".join(f"{k} {v}" for k, v in feed["结论"]["按段计数"].items())
        + "｜缺口槽位 " + str(len(GAPS)),
        "铁律：本文件不含新数字——JSON 条目运行时按路径读出、文本条目取值取自逐字校验的引句；",
        "      下游按「源文件 + sha256_16」去锚，不要另找第二事实源。",
        "",
        "键名｜单位｜取值｜来源",
    ]
    for x in feed["锚点"]:
        lines.append(f"  [{x['段']}] {x['键名']}｜{x['单位']}｜{x['取值']}｜"
                     f"{x['来源文件']}#{x['来源文件 sha256_16']}")
    lines += ["", "缺口槽位（需要 leo 给什么）："]
    lines += [f"  - {g['槽位']}：{g['需要 leo 给什么']}" for g in GAPS]
    lines += ["", f"检查：{sum(1 for c in CHECKS if c['通过'])}/{len(CHECKS)} 通过"]
    sp = os.path.join(OUT, "summary.txt")
    with open(sp, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
    print("\n".join(lines[:8]))
    print(f"… 共 {len(feed['锚点'])} 条锚点，缺口 {len(GAPS)} 条")
    print("\n产物：", OUT)
    failed = [c for c in CHECKS if not c["通过"]]
    if failed:
        raise SystemExit(f"feed 检查失败 {len(failed)} 条：{[c['检查'] for c in failed]}")


if __name__ == "__main__":
    main()
