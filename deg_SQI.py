# Python imports
from hashlib import shake_128

# SageMath imports
from sage.all import randint, ZZ, factor, proof, primes_first_n

# Local imports
from ideals import (
    is_integral,
    is_cyclic,
    multiply_ideals,
    equivalent_left_ideals,
    left_isomorphism,
)
from isogenies import torsion_basis, dual_isogeny, EllipticCurveIsogenyFactored
from deuring import IdealToIsogenyFromKLPT, kernel_to_ideal
from KLPT import RepresentIntegerHeuristic, SigningKLPT
from compression import compression, decompression
from utilities import inert_prime, has_order_D
from setup import E0, O0, Bτ, eτ, p, l, Dc, T_prime, ω, e, f_step_max
proof.all(False)


class deg_SQI(SQISign):
    def deg_commitment(self):
        """
        Compute the challenge isogeny and corresponding ideal
        of degree / norm T_prime

        Input: None
        Output: E1: the codomain of the commitment isogeny

        Stores to self:
        self.commitment_secrets = (ψ_ker, ψ, Iψ))
            ψ_ker: the kernel of ψ
            ψ: the secret commitment isogeny ψ : EA → E1
            Iψ: the ideal equivalent to ψ.
        """
        # Generate a random kernel
        # of order T_prime
        P, Q = torsion_basis(self.pk, T_prime)
        x = randint(1, T_prime)
        ψ_ker = P + x * Q

        # Generate the ideal Iψ from ψ_ker
        Iψ = kernel_to_ideal(ψ_ker, T_prime, [self.sk[0], self.sk[0].dual()])
        assert Iψ.norm() == T_prime, "Iψ has the wrong norm"

        # Generate the ideal ψ and its codomain
        ψ = EllipticCurveIsogenyFactored(self.pk, ψ_ker, order=T_prime)
        E1 = ψ.codomain()

        # Store secret results
        self.commitment_secrets = (ψ_ker, ψ, Iψ)

        return E1
    
    def deg_commitment_naive(self):
        """
        Compute the challenge isogeny and corresponding ideal
        of degree / norm T_prime

        Input: None
        Output: E1: the codomain of the commitment isogeny

        Stores to self:
        self.commitment_secrets = (ψ_ker, ψ, Iψ))
            ψ_ker: the kernel of ψ
            ψ: the secret commitment isogeny ψ : E0 → E1
            Iψ: the ideal equivalent to ψ.
        """
        # Generate a random kernel
        # of order T_prime
        T_l = available_torsion/T 
        P, Q = torsion_basis(E0, T_l)
        x = randint(1, T_l)
        ψ_ker = P + x * Q

        # Generate the ideal Iψ from ψ_ker
        Iψ = kernel_to_ideal(ψ_ker, T_l)
        assert Iψ.norm() == T_l, "Iψ has the wrong norm"

        # Generate the ideal ψ and its codomain
        ψ = EllipticCurveIsogenyFactored(E0, ψ_ker, order=T_l)
        E1 = ψ.codomain()

        # Store secret results
        self.commitment_secrets = (ψ_ker, ψ, Iψ)

        return E1, T_l


    def deg_challenge(self):
        CH = [p_tup[0] for p_tup in factor(available_torsion)]
        CH.remove(2)
        print(f"INFO [deg_SQI Challenge]: {len(CH)} bits avaible for challenge")

        deg = 1
        for q in CH:
            if randint(0,1):
                deg = deg*q

        return deg

    def deg_response_naive(self, ch, E1):
        """
        Compute the isogeny σ : EA → E1 of degree l^e*ch where
        e is a SQISign parameter. Does this by via the Deuring
        correspondence from an ideal of norm l^e.

        Input:  ch: an odd smooth integer 
                E1: the committed curve
        Output: S: a bitstring corresponding to an isogeny σ : EA → E2
        """
        if self.pk is None or self.sk is None:
            raise ValueError(f"Must first generate a keypair with `self.keygen()`")

        if self.commitment_secrets is None:
            raise ValueError(
                f"Must first generate a commitment with `self.commitment()`"
            )

        # Extract secret values from keygen
        EA = self.pk
        τ_prime, Iτ, Jτ = self.sk

        # Extract values from commitment
        ψ_ker, ψ, Iψ = self.commitment_secrets

        # Recover the dual of ψ from ψ and its kernel
        ψ_dual = dual_isogeny(ψ, ψ_ker, order=T_prime)

        # Deviation from paper time!
        # We are asked to first compute Iϕ
        # Then compute: Iτ_bar * Iψ * Iϕ
        # But we don't actually do this.
        # Instead, we directly compute
        # Iψ * Iϕ = Iψ ∩ I_([ψ]^* ϕ)
        #         = Iψ ∩ I_([ψ_dual]_* ϕ)
        #

        # First compute the ideal from the pullback
        # I_([ψ_dual]_* ϕ)

        E1.set_order((p**2 - 1) ** 2)
        P,Q = E1.torsion_basis(ch)
        x = randint(1, ch)
        ϕ_ker = P + x * Q

        Iϕ_pullback = kernel_to_ideal(ψ_dual(ϕ_ker), ch)
        IψIϕ = Iψ.intersection(Iϕ_pullback)
        print(IψIϕ.norm(),Iψ.norm(),Iϕ_pullback.norm(),Iψ.norm() * Iϕ_pullback.norm())
        print()
        assert IψIϕ.norm() == Iψ.norm() * Iϕ_pullback.norm()

        # Compute the product of ideals
        # I = Iτ_bar * Iψ * Iϕ
        Iτ_bar = Iτ.conjugate()
        I = multiply_ideals(Iτ_bar, IψIϕ)
        assert I.norm() == Iτ_bar.norm() * IψIϕ.norm()

        print(f"INFO [SQISign Response]: Running SigningKLPT")
        J = deg_SigningKLPT(I, Iτ)
        assert J.norm() == l**e, "SigningKLPT produced an ideal with incorrect norm"
        print(f"INFO [SQISign Response]: Finished SigningKLPT")

        assert equivalent_left_ideals(
            I, J
        ), "Signing KLPT did not produce an equivalent ideal!"
        assert is_cyclic(J), "SigningKLPT produced a non-cyclic ideal"

        # Ensure that the left and right orders match
        α = left_isomorphism(Iτ, Jτ)
        J = α ** (-1) * J * α
        assert J.left_order() == Jτ.right_order()

        print(f"INFO [SQISign Response]: Computing the corresponding isogeny")
        σ = IdealToIsogenyFromKLPT(J, Jτ, τ_prime, K_prime=Iτ)
        print(f"INFO [SQISign Response]: Computed the isogeny EA → E2")

        print(f"INFO [SQISign Response]: Compressing the isogeny σ to a bitstring")
        S = compression(EA, σ, l, f_step_max)
        print(
            f"INFO [SQISign Response]:"
            f"Compressed the isogeny σ to a bitstring of length {len(S)}"
        )

        return S


    def deg_response(self, ch, E1):
        """
        Compute the isogeny σ : EA → E1 of degree l^e*ch where
        e is a SQISign parameter. Does this by via the Deuring
        correspondence from an ideal of norm l^e.

        Input:  ch: an odd smooth integer 
                E1: the committed curve obtained using ψ : E0 → E1
        Output: S: a bitstring corresponding to an isogeny σ : EA → E1
        """
        if self.pk is None or self.sk is None:
            raise ValueError(f"Must first generate a keypair with `self.keygen()`")

        if self.commitment_secrets is None:
            raise ValueError(
                f"Must first generate a commitment with `self.commitment()`"
            )

        # Extract secret values from keygen
        EA = self.pk
        τ_prime, Iτ, Jτ = self.sk

        # Extract values from commitment
        ψ_ker, ψ, Iψ = self.commitment_secrets

        # Recover the dual of ψ from ψ and its kernel
        ψ_dual = dual_isogeny(ψ, ψ_ker, order=T_prime)

        # Compute the product of ideals
        # I = Iτ_bar * Iψ 
        Iτ_bar = Iτ.conjugate()
        I = multiply_ideals(Iτ_bar, Iψ)
        assert I.norm() == Iτ_bar.norm() * Iψ.norm()

        print('-----------------------------------------------')

        # ok, we have the ideal associated to EA → E1, now we need it to be of degree l^e*ch 
 
        print(f"INFO [SQISign Response]: Running SigningKLPT")
        J = deg_SigningKLPT(I, Iτ, ch)
        Jnorm = Integer(J.norm())
        print(J,'has norm',Jnorm)

        assert Jnorm == ch*Jnorm.p_primary_part(2), "SigningKLPT produced an ideal with incorrect norm"
        print(f"INFO [SQISign Response]: Finished SigningKLPT")

        assert equivalent_left_ideals(
            I, J
        ), "Signing KLPT did not produce an equivalent ideal!"
        assert is_cyclic(J), "SigningKLPT produced a non-cyclic ideal"

        # Ensure that the left and right orders match
        α = left_isomorphism(Iτ, Jτ)
        J = α ** (-1) * J * α
        assert J.left_order() == Jτ.right_order()

        eJ = J.norm().valuation(2)
        print('valuation',eJ)
        assert ch*(2**eJ) == J.norm(), 'norm not as expected'
        # O =  J.left_order()
        # J2 = J + (2**eJ) * O
        # Jch = invert_ideal(J2)*J 
        Jch = J + ch*J.right_order()
        J2 = multiply_ideals(J,invert_ideal(Jch))
        assert Jch.norm() == ch, 'Jch of the wrong norm'
        assert is_cyclic(Jch), 'Jch not cyclic'
        assert 2**(J2.norm().valuation(2)) == J2.norm(), 'J2 is not 2-smooth'
        assert is_cyclic(J2), 'J2 not cyclic'



        print(f"INFO [SQISign Response]: Computing the corresponding isogeny for the 2-smooth part")
        # this part doe
        σ2,I2 = IdealToIsogenyFromKLPT_deg(J2, Jτ, τ_prime, K_prime=Iτ)
        print(f"INFO [SQISign Response]: Computed the isogeny EA → E/E[J2]")
        assert σ2.domain() == EA, 'Domain different from expected'

        # I2 = multiply_ideals(Jτ,J2) # I2 connects E0 to E/E[J2]
        assert I2.right_order() == Jch.left_order(), 'ideals computed are strange'

        assert 2**(I2.norm().valuation(2)) == I2.norm(), 'I2 is not 2-smooth'

        assert is_cyclic(I2), 'I2 not cyclic'
        I2 = make_cyclic(I2) # TODO assert ... 
        print(f"INFO [SQISign Response]: Computing the corresponding isogeny for the ch part")

        I2starJch = pullback_ideal(O0,Jch.left_order(),Jch,I2)

        assert is_cyclic(I2starJch), 'I2starJch not cyclic'


        K_pulled = ideal_to_kernel(E0,I2starJch)
        K = σ2(τ_prime(K_pulled))

        σch = EllipticCurveIsogenyFactored(σ2.codomain(),K, order = ch)
        σ = σch * σ2 

        assert σ.codomain().j_invariant() == E1.j_invariant(), 'codomain of σ not as expected'


        print(f"INFO [SQISign Response]: Computed the isogeny EA → E/E[J]")


        # print(f"INFO [SQISign Response]: Compressing the isogeny σ to a bitstring")
        # S = compression(EA, σ, l, f_step_max)
        # print(
        #     f"INFO [SQISign Response]:"
        #     f"Compressed the isogeny σ to a bitstring of length {len(S)}"
        # )

        return σ,σch, σ2 ,J



if __name__ == "__main__":
    load("setup.py")
    load("SQISign.py")
    load('KLPT.py')
    t = deg_SQI()
    t.keygen()
    # E1, T_l = t.deg_commitment_naive()
    E1 = t.commitment()
    print('com = ',E1)
    print(t.commitment_secrets)
    ch = t.deg_challenge()
    σ,σ1,σ2,J = t.deg_response(ch, E1)

    print('ch  = ',ch.factor())
    print('Degree of σ :',σ.degree().factor())
    


    


