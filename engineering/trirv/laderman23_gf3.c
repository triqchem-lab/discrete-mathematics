/* engineering/trirv/laderman23_gf3.c — M17: Laderman-23 在 GF(3) 上的三进制 VM 独立核验
 *
 * 被核验对象: GF(3) 上 ⟨3,3,3⟩ 的 23 项秩分解（与 src/Sovereign/Algebra/LinearAlgebra/
 * TensorRankLadermanGF3.agda 同一证书; 打包表 PK 由 engineering/oracle_rank3_witness_gf3.py
 * 的表发射: 第 k 门 = PK[k], PK[23+k], PK[46+k] 三个字, 每字 9 个三进制位, 低 3^0 位 = 行主序位置 0;
 * 值 2 读回成 -1）。打包原因: 621 个字会撑爆 16K 数据区, 打包后 69 字。
 *
 * 算法: 逐门解包 27 个系数, 外积累进 ACC[729]; 再对 729 个 (x,y,z) 逐点核对
 *   ACC 归约到 {0,1,2} 后 == mm(x,y,z) = [行x=行z][列x=行y][列y=列z]。
 *
 * 返回值 = mism*4 + (27-hits)*2 + (fires-27); 全对（mism=0, hits=27, fires=27）时为 0。
 * 负控制（PK[12] 最低位三进制位 2->0）: oracle 侧模拟预言 bad=16, hits=26 ⇒ 返回 66。
 *
 * C 三值方言纪律（~/ai-lab/trirv/docs/C-TERNARY-PITFALLS.md）: 全文不用 & | ^ ~ << >>;
 *   归约用 while 加减 3; 行/列查表, 不用位运算。
 *
 * 编译/运行: ~/ai-lab/trirv/cc/trirv_cc 本件 out.trv && ~/ai-lab/trirv/trirv_vm out.trv
 */

int PK[69] = {
  567, 2268, 6561, 486, 12809, 2187,
  4779, 19, 730, 9, 1458, 1469,
  513, 756, 12705, 1755, 4389, 21,
  2190, 81, 27, 1, 3, 567,
  2268, 6561, 16624, 2187, 243, 2754,
  21, 2190, 12705, 9, 2208, 19,
  730, 729, 748, 1242, 513, 756,
  27, 3, 1, 81, 4455, 324,
  6561, 243, 2187, 10145, 4698, 4377,
  12, 9, 19236, 4386, 1485, 270,
  729, 1728, 1468, 1459, 10, 27,
  81, 1, 3
};

int ROW[9] = { 0, 0, 0, 1, 1, 1, 2, 2, 2 };
int COL[9] = { 0, 1, 2, 0, 1, 2, 0, 1, 2 };
int ACC[729];
int u9[9];
int v9[9];
int w9[9];

int main(){
  int i = 0;
  while (i < 729) { ACC[i] = 0; i = i + 1; }
  int k = 0;
  while (k < 23) {
    int p = PK[k];
    int a = 0;
    while (a < 9) {
      int t = p - (p/3)*3;
      if (t == 2) { t = 0 - 1; }
      u9[a] = t;
      p = p / 3;
      a = a + 1;
    }
    p = PK[23 + k];
    a = 0;
    while (a < 9) {
      int t = p - (p/3)*3;
      if (t == 2) { t = 0 - 1; }
      v9[a] = t;
      p = p / 3;
      a = a + 1;
    }
    p = PK[46 + k];
    a = 0;
    while (a < 9) {
      int t = p - (p/3)*3;
      if (t == 2) { t = 0 - 1; }
      w9[a] = t;
      p = p / 3;
      a = a + 1;
    }
    int ax = 0;
    while (ax < 9) {
      int ay = 0;
      while (ay < 9) {
        int az = 0;
        while (az < 9) {
          ACC[ax*81 + ay*9 + az] = ACC[ax*81 + ay*9 + az] + u9[ax]*v9[ay]*w9[az];
          az = az + 1;
        }
        ay = ay + 1;
      }
      ax = ax + 1;
    }
    k = k + 1;
  }
  int mism = 0;
  int hits = 0;
  int fires = 0;
  int cx = 0;
  while (cx < 9) {
    int cy = 0;
    while (cy < 9) {
      int cz = 0;
      while (cz < 9) {
        int s = ACC[cx*81 + cy*9 + cz];
        while (s < 0) { s = s + 3; }
        while (s > 2) { s = s - 3; }
        int e = 0;
        if (ROW[cx] == ROW[cz]) {
          if (COL[cx] == ROW[cy]) {
            if (COL[cy] == COL[cz]) { e = 1; }
          }
        }
        fires = fires + e;
        if (s != e) { mism = mism + 1; }
        if (e == 1) {
          if (s == 1) { hits = hits + 1; }
        }
        cz = cz + 1;
      }
      cy = cy + 1;
    }
    cx = cx + 1;
  }
  return mism*4 + (27 - hits)*2 + (fires - 27);
}
