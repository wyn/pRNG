# pRNG - An implementation of Random123 - a Counter-based Pseudo Random Number generator,
# http://www.thesalmons.org/john/random123/releases/latest/docs/index.html


import smartpy as sp


@sp.module
def main():
    four_digit: type = sp.record(i0=sp.nat, i1=sp.nat, i2=sp.nat, i3=sp.nat)

    max_int = 18446744073709551616  # 2 ^ 64
    max_rounds = 72

    rot_num00 = 14
    rot_num01 = 52
    rot_num02 = 23
    rot_num03 = 5
    rot_num04 = 25
    rot_num05 = 46
    rot_num06 = 58
    rot_num07 = 32

    rot_num10 = 16
    rot_num11 = 57
    rot_num12 = 40
    rot_num13 = 37
    rot_num14 = 33
    rot_num15 = 12
    rot_num16 = 22
    rot_num17 = 32

    class Threefry4x64(sp.Contract):
        def __init__(self, nrounds):
            assert nrounds <= max_rounds
            self.data.nrounds = nrounds
            self.data.result = sp.cast(None, sp.option[four_digit])

        @sp.private
        def rotL(self, x, n):
            l = n & 63
            left = sp.mod(x << l, max_int)
            diff = sp.to_int(64) - sp.to_int(n)
            r = sp.as_nat(diff) & 63
            right = sp.mod(x >> r, max_int)
            return left | right

        @sp.private
        def aux1(self, lbound, nrounds, x, i_0, i_1, rotL):
            # if(Nrounds>0){                                                      \
            #     X0 += X1; X1 = RotL_##W(X1,R_##W##x4_0_0); X1 ^= X0; \
            #     X2 += X3; X3 = RotL_##W(X3,R_##W##x4_0_1); X3 ^= X2; \
            # }                                                                   \
            assert nrounds > lbound
            x0 = sp.mod(x.i0 + x.i1, max_int)
            x1 = rotL(sp.record(x=x.i1, n=i_0))
            x1 = x1 ^ x0

            x2 = sp.mod(x.i2 + x.i3, max_int)
            x3 = rotL(sp.record(x=x.i3, n=i_1))
            x3 = x3 ^ x2
            return sp.record(i0=x0, i1=x1, i2=x2, i3=x3)

        @sp.private
        def aux2(self, lbound, nrounds, x, i_0, i_1, rotL):
            # if(Nrounds>1){                                                      \
            #     X0 += X3; X3 = RotL_##W(X3,R_##W##x4_1_0); X3 ^= X0; \
            #     X2 += X1; X1 = RotL_##W(X1,R_##W##x4_1_1); X1 ^= X2; \
            # }                                                                 )
            assert nrounds > lbound
            x0 = sp.mod(x.i0 + x.i3, max_int)
            x3 = rotL(sp.record(x=x.i3, n=i_0))
            x3 = x3 ^ x0

            x2 = sp.mod(x.i2 + x.i1, max_int)
            x1 = rotL(sp.record(x=x.i1, n=i_1))
            x1 = x1 ^ x2
            return sp.record(i0=x0, i1=x1, i2=x2, i3=x3)

        @sp.private
        def aux3(self, lbound, nrounds, x, y0, y1, y2, y3, i):
            # if(Nrounds>3){                                                      \
            #     /* InjectKey(r=1) */                                            \
            #     X0 += ks1; X1 += ks2; X2 += ks3; X3 += ks4; \
            #     X3 += 1;     /* XWCNT4-1 += r  */                 \
            # }                                                                   \ *)
            assert nrounds > lbound
            x0 = sp.mod(x.i0 + y0, max_int)
            x1 = sp.mod(x.i1 + y1, max_int)
            x2 = sp.mod(x.i2 + y2, max_int)
            x3 = sp.mod(x.i3 + y3, max_int)
            x3 = sp.mod(x3 + i, max_int)
            return sp.record(i0=x0, i1=x1, i2=x2, i3=x3)

        @sp.private
        def skein_ks_parity_(self, hi, lo):
            # let skein_ks_parity =
            #   let hi = "0x1BD11BDA" |> of_string in
            #   let lo = "0xA9FC1A22" |> of_string in
            #   add lo (U.shift_left hi 32)
            return sp.mod(lo + sp.mod((hi << 32), max_int), max_int)

        @sp.entrypoint
        def rand(self, key, ctr):
            nrounds = self.data.nrounds

            ks4 = self.skein_ks_parity_(sp.record(hi=466688986, lo=2851871266))

            ks0 = key.i0
            x0 = sp.mod(ctr.i0 + ks0, max_int)
            ks4 = ks4 ^ ks0

            ks1 = key.i1
            x1 = sp.mod(ctr.i1 + ks1, max_int)
            ks4 = ks4 ^ ks1

            ks2 = key.i2
            x2 = sp.mod(ctr.i2 + ks2, max_int)
            ks4 = ks4 ^ ks2

            ks3 = key.i3
            x3 = sp.mod(ctr.i3 + ks3, max_int)
            ks4 = ks4 ^ ks3

            x = sp.record(i0=x0, i1=x1, i2=x2, i3=x3)

            x = self.aux1(
                sp.record(
                    lbound=0,
                    nrounds=nrounds,
                    x=x,
                    i_0=rot_num00,
                    i_1=rot_num10,
                    rotL=self.rotL,
                )
            )
            x = self.aux2(
                sp.record(
                    lbound=1,
                    nrounds=nrounds,
                    x=x,
                    i_0=rot_num01,
                    i_1=rot_num11,
                    rotL=self.rotL,
                )
            )
            x = self.aux1(
                sp.record(
                    lbound=2,
                    nrounds=nrounds,
                    x=x,
                    i_0=rot_num02,
                    i_1=rot_num12,
                    rotL=self.rotL,
                )
            )
            x = self.aux2(
                sp.record(
                    lbound=3,
                    nrounds=nrounds,
                    x=x,
                    i_0=rot_num03,
                    i_1=rot_num13,
                    rotL=self.rotL,
                )
            )
            x = self.aux3(
                sp.record(
                    lbound=3, nrounds=nrounds, x=x, y0=ks1, y1=ks2, y2=ks3, y3=ks4, i=1
                )
            )

            x = self.aux1(
                sp.record(
                    lbound=4,
                    nrounds=nrounds,
                    x=x,
                    i_0=rot_num04,
                    i_1=rot_num14,
                    rotL=self.rotL,
                )
            )
            x = self.aux2(
                sp.record(
                    lbound=5,
                    nrounds=nrounds,
                    x=x,
                    i_0=rot_num05,
                    i_1=rot_num15,
                    rotL=self.rotL,
                )
            )
            x = self.aux1(
                sp.record(
                    lbound=6,
                    nrounds=nrounds,
                    x=x,
                    i_0=rot_num06,
                    i_1=rot_num16,
                    rotL=self.rotL,
                )
            )
            x = self.aux2(
                sp.record(
                    lbound=7,
                    nrounds=nrounds,
                    x=x,
                    i_0=rot_num07,
                    i_1=rot_num17,
                    rotL=self.rotL,
                )
            )
            x = self.aux3(
                sp.record(
                    lbound=7, nrounds=nrounds, x=x, y0=ks2, y1=ks3, y2=ks4, y3=ks0, i=2
                )
            )

            x = self.aux1(
                sp.record(
                    lbound=8,
                    nrounds=nrounds,
                    x=x,
                    i_0=rot_num00,
                    i_1=rot_num10,
                    rotL=self.rotL,
                )
            )
            x = self.aux2(
                sp.record(
                    lbound=9,
                    nrounds=nrounds,
                    x=x,
                    i_0=rot_num01,
                    i_1=rot_num11,
                    rotL=self.rotL,
                ),
            )
            x = self.aux1(
                sp.record(
                    lbound=10,
                    nrounds=nrounds,
                    x=x,
                    i_0=rot_num02,
                    i_1=rot_num12,
                    rotL=self.rotL,
                )
            )
            x = self.aux2(
                sp.record(
                    lbound=11,
                    nrounds=nrounds,
                    x=x,
                    i_0=rot_num03,
                    i_1=rot_num13,
                    rotL=self.rotL,
                )
            )
            x = self.aux3(
                sp.record(
                    lbound=11, nrounds=nrounds, x=x, y0=ks3, y1=ks4, y2=ks0, y3=ks1, i=3
                )
            )

            x = self.aux1(
                sp.record(
                    lbound=12,
                    nrounds=nrounds,
                    x=x,
                    i_0=rot_num04,
                    i_1=rot_num14,
                    rotL=self.rotL,
                )
            )
            x = self.aux2(
                sp.record(
                    lbound=13,
                    nrounds=nrounds,
                    x=x,
                    i_0=rot_num05,
                    i_1=rot_num15,
                    rotL=self.rotL,
                )
            )
            x = self.aux1(
                sp.record(
                    lbound=14,
                    nrounds=nrounds,
                    x=x,
                    i_0=rot_num06,
                    i_1=rot_num16,
                    rotL=self.rotL,
                )
            )
            x = self.aux2(
                sp.record(
                    lbound=15,
                    nrounds=nrounds,
                    x=x,
                    i_0=rot_num07,
                    i_1=rot_num17,
                    rotL=self.rotL,
                )
            )
            x = self.aux3(
                sp.record(
                    lbound=15, nrounds=nrounds, x=x, y0=ks4, y1=ks0, y2=ks1, y3=ks2, i=4
                )
            )

            x = self.aux1(
                sp.record(
                    lbound=16,
                    nrounds=nrounds,
                    x=x,
                    i_0=rot_num00,
                    i_1=rot_num10,
                    rotL=self.rotL,
                )
            )
            x = self.aux2(
                sp.record(
                    lbound=17,
                    nrounds=nrounds,
                    x=x,
                    i_0=rot_num01,
                    i_1=rot_num11,
                    rotL=self.rotL,
                )
            )
            x = self.aux1(
                sp.record(
                    lbound=18,
                    nrounds=nrounds,
                    x=x,
                    i_0=rot_num02,
                    i_1=rot_num12,
                    rotL=self.rotL,
                )
            )
            x = self.aux2(
                sp.record(
                    lbound=19,
                    nrounds=nrounds,
                    x=x,
                    i_0=rot_num03,
                    i_1=rot_num13,
                    rotL=self.rotL,
                )
            )
            x = self.aux3(
                sp.record(
                    lbound=19, nrounds=nrounds, x=x, y0=ks0, y1=ks1, y2=ks2, y3=ks3, i=5
                )
            )

            self.data.result = sp.Some(x)


if "main" in __name__:

    @sp.add_test()
    def test():
        scenario = sp.test_scenario("Threefry4x64", [sp.math, main])
        c1 = main.Threefry4x64(20)
        scenario.h1("Random123 on-chain")
        scenario += c1

        # test with some of the KAT test data for nrounds=20:
        # https://github.com/DEShawResearch/random123/blob/9545ff6413f258be2f04c1d319d99aaef7521150/tests/kat_vectors#L78
        key = sp.record(i0=0, i1=0, i2=0, i3=0)
        ctr = sp.record(i0=0, i1=0, i2=0, i3=0)
        c1.rand(sp.record(key=key, ctr=ctr))
        r = c1.data.result.unwrap_some()
        scenario.show(r)
        scenario.verify(r.i0 == 657963966844654903)
        scenario.verify(r.i1 == 6166588228550287621)
        scenario.verify(r.i2 == 5463532747209585884)
        scenario.verify(r.i3 == 17161507908560806923)

        ff = 18446744073709551616 - 1  # 2 ^ 64 - 1
        key = sp.record(i0=ff, i1=ff, i2=ff, i3=ff)
        ctr = sp.record(i0=ff, i1=ff, i2=ff, i3=ff)
        c1.rand(sp.record(key=key, ctr=ctr))
        r = c1.data.result.unwrap_some()
        scenario.show(r)
        scenario.verify(r.i0 == 3009038520807045659)
        scenario.verify(r.i1 == 248186141452226065)
        scenario.verify(r.i2 == 4333342425934739996)
        scenario.verify(r.i3 == 14783366217828847976)
