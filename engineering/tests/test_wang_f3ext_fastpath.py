"""F₃ 求秩 / 展平秩快路径（Wang 框架 core/rank_f3_fast.h）的等价性回归测试。

背景（2026-11-27）: 框架的通用 DynamicMatrix<3,1>::Rank() 每次调用堆分配 + 全 Gauss–Jordan,
RankLowerBoundFlatten 再做两次循环转置 + 三次堆分配; forced product 每次迭代约 20 µs,
3^18 = 3.87 亿次枚举要 16 分钟。F₃ 扩展给这两处加了快路径（前向消元 + 栈上平铺数组 + 直接按跨度读取）。
本测试编译 engineering/wang_f3ext/standalone/rank_f3_fast_check.cc, 用**独立写的**参考实现做随机对拍。

需要上游副本（WANG_REPO, 缺省 /tmp/wang-tensor-rank）已打补丁; 缺失时跳过（/tmp 易失）。
"""
import os
import platform
import shutil
import subprocess
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
EXT = os.path.join(ROOT, "engineering", "wang_f3ext")
TEST_CC = os.path.join(EXT, "standalone", "rank_f3_fast_check.cc")


def _find_repo():
    repo = os.environ.get("WANG_REPO", "/tmp/wang-tensor-rank")
    if os.path.isdir(os.path.join(repo, "core")) and os.path.exists(os.path.join(repo, "core", "rank_f3_fast.h")):
        return repo
    return None


def _find_cxx():
    for cxx in (os.environ.get("CXX"), "/opt/homebrew/opt/llvm/bin/clang++", shutil.which("clang++"), shutil.which("g++")):
        if cxx and os.path.exists(cxx):
            return cxx
    return None


class WangF3extFastPathTest(unittest.TestCase):
    """F₃ 快路径与独立参考实现在随机输入上逐个相等（求秩 + 展平秩）。"""

    def test_rank_and_flatten_fast_paths_match_reference(self):
        repo = _find_repo()
        if repo is None:
            self.skipTest("上游副本未就绪（WANG_REPO 未打补丁）")
        cxx = _find_cxx()
        if cxx is None:
            self.skipTest("no C++ compiler found")
        with tempfile.TemporaryDirectory() as tmp:
            exe = os.path.join(tmp, "rank_f3_fast_check")
            build = subprocess.run(
                [cxx, "-std=c++23", "-O2", "-DNDEBUG", "-w", "-pthread",
                 "-I" + os.path.join(EXT, "shim"), "-I" + repo, TEST_CC,
                 os.path.join(repo, "core", "dynamic_matrix.cc"), "-o", exe],
                capture_output=True, text=True, timeout=600,
            )
            self.assertEqual(build.returncode, 0, build.stderr[-2000:])
            run = subprocess.run([exe, "4000"], capture_output=True, text=True, timeout=600)
            self.assertEqual(run.returncode, 0, run.stdout[-1500:])
            self.assertIn("mismatches=0", run.stdout)
            self.assertNotIn("MISMATCH", run.stdout)

    def test_get_batch_kernel(self):
        """OrbitMap::Get 的批量探针内核(NEON 16 路 + 标签预筛): 块内核 / 端到端 / 未命中三项对拍 + 微基准(需 ARM64)。"""
        repo = _find_repo()
        if repo is None:
            self.skipTest("上游副本未就绪（WANG_REPO 未打补丁）")
        if platform.machine() not in ("arm64", "aarch64"):
            self.skipTest("批量探针内核的 NEON 版需要 ARM64")
        cxx = _find_cxx()
        if cxx is None:
            self.skipTest("no C++ compiler found")
        src = os.path.join(EXT, "standalone", "get_simd_check.cc")
        with tempfile.TemporaryDirectory() as tmp:
            exe = os.path.join(tmp, "get_simd_check")
            build = subprocess.run(
                [cxx, "-std=c++23", "-O2", "-DNDEBUG", "-w", "-pthread",
                 "-I" + os.path.join(EXT, "shim"), "-I" + repo, src,
                 os.path.join(repo, "core", "dynamic_matrix.cc"), "-o", exe],
                capture_output=True, text=True, timeout=900,
            )
            self.assertEqual(build.returncode, 0, build.stderr[-2000:])
            run = subprocess.run([exe, "60"], capture_output=True, text=True, timeout=900)
            self.assertEqual(run.returncode, 0, run.stdout[-1500:])
            self.assertEqual(run.stdout.count("mismatches=0"), 3, run.stdout)
            self.assertNotIn("MISMATCH", run.stdout)
            self.assertIn("OK", run.stdout)

    def test_group_action_fast_path_matches_naive(self):
        """F₃ 3×3 群作用快路径 vs 独立朴素实现（全量 19683 向量 × 全部群元; 默认抽样步长 17, WANG_SLOW=1 全量）。"""
        repo = _find_repo()
        if repo is None:
            self.skipTest("上游副本未就绪（WANG_REPO 未打补丁）")
        cxx = _find_cxx()
        if cxx is None:
            self.skipTest("no C++ compiler found")
        src = os.path.join(EXT, "standalone", "apply_check.cc")
        with tempfile.TemporaryDirectory() as tmp:
            exe = os.path.join(tmp, "apply_check")
            build = subprocess.run(
                [cxx, "-std=c++23", "-O2", "-DNDEBUG", "-w", "-pthread",
                 "-I" + os.path.join(EXT, "shim"), "-I" + repo, src,
                 os.path.join(repo, "core", "dynamic_matrix.cc"), "-o", exe],
                capture_output=True, text=True, timeout=600,
            )
            self.assertEqual(build.returncode, 0, build.stderr[-2000:])
            stride = "1" if os.environ.get("WANG_SLOW") else "17"
            run = subprocess.run([exe, stride], capture_output=True, text=True, timeout=900)
            self.assertEqual(run.returncode, 0, run.stdout + run.stderr[-800:])
            self.assertIn("mismatches: store=0 query=0 inverse=0 identity=0", run.stdout)


if __name__ == "__main__":
    unittest.main()
