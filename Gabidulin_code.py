from __future__ import absolute_import
from sage.matrix.constructor import matrix, diagonal_matrix
from sage.matrix.matrix import is_Matrix
from sage.structure.element import is_Vector
from sage.sets.set import Set
from sage.matrix.constructor import column_matrix
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.categories.cartesian_product import cartesian_product
from sage.modules.free_module_element import vector
from sage.modules.free_module import VectorSpace
from sage.rings.integer import Integer
from sage.misc.cachefunc import cached_method
from sage.rings.integer_ring import ZZ
from sage.functions.other import floor
from sage.coding.linear_code import AbstractLinearCode
from sage.coding.relative_finite_field_extension import *
from sage.structure.sage_object import SageObject
from sage.functions.log import *
from sage.rings.polynomial.skew_polynomial_element import *
from sage.coding.encoder import Encoder
#from sage.coding.channel_constructions import Channel
from sage.coding.decoder import Decoder, DecodingError


r"""
Gabidulin Code

Let $\\GF{q^m}$ be a finite field considered as an extension field over $\\GF{q}$. 
A Gabidulin code is denoted by `$Gab[n,k]$` , where `$n$` being the length of the
code and `$k$` its dimension. Elements of a code `$Gab[n,k]$` are called codewords.
Given the code parameters $(n,k)$, a finite field $\\GF{q}$ and its extension field $\\GF{q^m}$
the corresponding Gabidulin Code is the set:

.. MATH::

    Gab[n,k] = \{ (f(g_0),f(g_1),\cdots,f(g_{n-1})) | \quad deg_{q}(f(x))< k \}

This file contains the following elements:

    - :class:`GabidulinCode`, the class for Gabidulin codes over $\\GF{q^m}$
    - :class:`GabidulinCodeGeneratorMatrixEncoder`, an encoder of an information vector using the code generator matrix.
    - :class:`GabidulinCodePolynomialEvaluationEncoder`, an encoder that evaluates a linearized polynomial 
							using a set of linearly independent points.
"""

class GabidulinCode(AbstractLinearCode):
	r"""
	Class for Gabidulin codes $Gab[n,k]$.

	INPUT:

		- ``ground_field`` -- A finite field $\\GF{q}$ of a prime power order $q$.

		- ``extension_field`` -- A finite field $\\GF{q^m}$ which is an extension field of degree $m$ of $\\GF{q}$.

		- ``length`` -- The length of the Gabidulin Code, i.e., length $(n)$ should be less than or equal to $(m)$.

		- ``dimension`` -- The dimesnion of the Gabidulin Code, i.e., dimension $(k)$ should be less than or equal to the length $(n)$.


	EXAMPLES::

		sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
		sage: F.<t> = GF(4)
		sage: Fm.<tt> = GF(4^3)
		sage: n=3
		sage: k=2
		sage: q = F.order()
		sage: p = F.characteristic()
		sage: Frob = Fm.frobenius_endomorphism(log(q,p))
		sage: L.<x>=Fm['x',Frob]
		sage: C=GabidulinCode(F,Fm,L,n,k)
		sage: C
		Gabidulin Code Gab[3,2] over Finite Field in tt of size 2^6
	"""
	_registered_encoders = {}
	_registered_decoders = {}

	def __init__(self, ground_field, extension_field, linearized_poly_ring, length, dimension):
		r"""
		Notes:

		1. Length of the code must be a positive integer less than or equal to the extension degree $(m)$::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,4,2)
			Traceback (click to the left of this block for traceback)
				...
				ValueError: length of the code must be a positive integer less than or
				equal to the extension degree (m) = 3

		2. Dimension of the code must be a positive integer less than or equal to the length of the code $(n)$::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,3,4)
				Traceback (click to the left of this block for traceback)
				...
				ValueError: dimension of the code must be a positive integer less than
				or equal to the length of the code (n) = 3

		3. The extension_field should be a field extension of the finite ground_field.

		"""		

		F  = ground_field
		Fm = extension_field
		FE = RelativeFiniteFieldExtension(Fm, F)
		m = FE.extension_degree() #Fm.degree()/F.degree()
		# input sanitization
		if not length <= m or length not in ZZ or length < 1:
			raise ValueError("length of the code must be a positive integer less than or equal to the extension degree (m) = %d" % m )
		if not dimension <= length or dimension not in ZZ or dimension < 1:
			raise ValueError("dimension of the code must be a positive integer less than or equal to the length of the code (n) = %d" % length )
		super(GabidulinCode, self).__init__(Fm, length, "EvaluationEncoder", "GabidulinGao")
		self._dimension = dimension
		self._length = length
		self._ground_field = F
		self._extension_field = Fm
		self._extension_degree = m
		self._relative_extension = FE
		self._linearized_poly_ring = linearized_poly_ring
		self._Frob = linearized_poly_ring.twist_map()

	def length(self):
		r"""
		Returns the length of ``self``.

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: C.length()
			
			3
		"""
		return self._length


    
    	def dimension(self):
		r"""
		Returns the dimension of ``self``.

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: C.dimension()

			2
		"""
		return self._dimension

    	def minimum_distance(self):
		r"""
		Returns the minimum distance of ``self``.

		Minimum distance, 

		.. MATH::

			d = n - k + 1

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: C.minimum_distance()
			2
		"""
		n = self._length
		k = self._dimension
		return (n-k+1)

	def linearized_poly_ring(self):
		r"""
		Returns the linearized polynomials ring of ``self`` over $\\GF{q^m}$ denoted by $\\mathcal{L_{q^m}}[x]$.

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: C.linearized_poly_ring()
			Skew Polynomial Ring in x over Finite Field in tt of size 2^6 twisted by
			tt |--> tt^(2^2)


		"""
		return self._linearized_poly_ring	
		
	def cardinality(self):
		r"""
		Returns the cardinality of ``self``.

		The code cardinality is the number of codewords in the code.

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: C.cardinality()
			4096
		"""
		m = self._extension_degree
		k = self._dimension
		q = self._ground_field.order()
		K = q**(m*k)
		return K
			
	def ground_field(self):
		r"""
		Returns the ground field $\\GF{q}$ of ``self``.

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: C.ground_field()
			Finite Field in t of size 2^2
		"""	
		return self._ground_field
		
	def extension_field(self):
		r"""
		Returns the extension field $\\GF{q^m}$ of ``self``.

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: C.extension_field()
			Finite Field in tt of size 2^6
		"""	
		return self._extension_field
		
	def extension_degree(self):
		r"""
		Returns the extension degree $(m)$ of an extension field $\\GF{q^m}$ over $\\GF{q}$ of ``self``.

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: C.extension_degree()
			3
		"""	
		return self._extension_degree
    	
	def rank_weight(self,codeword_in_vector_repr):
		r"""
		Returns the rank weight of a vector over $\\GF{q^m}$ of ``self``.

		Let  $\\mathbf{\\textit{x}} \\in \\GF{q^m}^n$ a word of length $n$ which could be spanned to a matrix $\\mathbf{\\textit{A}}  \\in \\GF{q}^{m \\times n}$. 
		Then, the Rank Weight denoted by $wt_R(\\mathbf{\\textit{x}})$ is the rank of the matrix $\\mathbf{\\textit{A}}$, that is:

		.. MATH:: 										
			wt_R(\mathbf{\textit{x}}) = Rk(\mathbf{\textit{x}}) = Rk(\mathbf{\textit{A}})

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: eval = C.evaluation_points()
			sage: C.rank_weight(eval)
			
			3
		"""
		codeword_in_matrix_repr = self.map_into_ground_field(codeword_in_vector_repr)
		rank_weight = codeword_in_matrix_repr.rank()
        	return rank_weight

	def rank_distance(self,codeword_in_vector_repr1,codeword_in_vector_repr2):
		r"""
		Returns the rank distance between two vectors over $\\GF{q^m}$ of ``self``.

		Let $\\mathbf{\\textit{x1}},\\mathbf{\\textit{x2}} \\in \\GF{q^m}^n$ be two words of length $n$ and $\\mathbf{\\textit{A1}}, \\mathbf{\\textit{A2}}
		\\in \\GF{q}^{m \\times n}$ be the matrix representations respectively. Then, the rank distance denoted by $d_R(\\mathbf{\\textit{x1}},\\mathbf{\\textit{x2}})$ 
		is the rank  of the difference between these two matrices, that is:

		.. MATH:: 										
			d_R(\mathbf{\textit{x1}},\mathbf{\textit{x2}}) = Rk(\mathbf{\textit{x1}}-\mathbf{\textit{x2}}) = Rk(\mathbf{\textit{A1}}-\mathbf{\textit{A2}})

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: eval = C.evaluation_points()
			sage: C.rank_distance(eval,[0*tt,0*tt,0*tt])

			3
		"""
		codeword_in_matrix_repr1 = self.map_into_ground_field(codeword_in_vector_repr1)
		codeword_in_matrix_repr2 = self.map_into_ground_field(codeword_in_vector_repr2)
		rank_distance = (codeword_in_matrix_repr1-codeword_in_matrix_repr2).rank()
		return rank_distance


	def polynomial_basis(self):
		r"""
		Returns the polynomial(power) basis of an extension_field $\\GF{q^m}$ over $\\GF{q}$ of ``self``.

		A polynomial basis is a basis of the form $( 1 , \\alpha^1, \\alpha^2, \\cdots, \\alpha^{m-1} )$

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: C.polynomial_basis()
	 		(1, tt, tt^2)

		"""	
		m = self._extension_degree
		FE = self._relative_extension		
		absolute_field_basis = FE.absolute_field_basis()
		basis = absolute_field_basis[0:m]	
		return vector(basis)

	@cached_method
	def normal_basis(self):
		r"""
		Returns a normal basis of an extension_field $\\GF{q^m}$ over $\\GF{q}$ of ``self``. 

		A normal basis is a basis of the form $( \\alpha , \\alpha^q, \\alpha^{q^2}, \\cdots, \\alpha^{q^{m-1}} )$,
 		where $(\\alpha)$ is a normal element in $\\GF{q^m}$. 


		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: C.normal_basis()
			(tt^5 + tt^4 + 1, tt^4 + tt^2 + 1, tt^5 + tt^2 + 1)
		"""	
		m = self._extension_degree
		F = self._ground_field
		Fm = self._extension_field
		V = VectorSpace(F,m)
		f=F.polynomial()
		alpha = f.any_root(Fm)
		g=f/((Fm.gen()-alpha)*f.derivative()(alpha))
		u=Fm.random_element()
		normal_element= g(u)
		normal_basis = [normal_element]
		for i in range(1,m):
			normal_basis.append(self.q_power(normal_element,i))
		basis_ground = self.map_into_ground_field(normal_basis)	
		while matrix(basis_ground).is_singular():
			u=Fm.random_element()
			normal_element= g(u)
			normal_basis = [normal_element]
			for i in range(1,m):
				normal_basis.append(self.q_power(normal_element,i))
		    	basis_ground = self.map_into_ground_field(normal_basis)
		self._is_normal_basis(normal_basis)
		return vector(normal_basis)
	
	def _is_normal_basis(self,normal_basis):
		r"""
		Checks if a given basis is a normal basis of an extension_field $\\GF{q^m}$ over $\\GF{q}$ of ``self``. 

		A normal basis is a basis of the form $( \\alpha , \\alpha^q, \\alpha^{q^2}, \\cdots, \\alpha^{q^{m-1}} )$,
 		where $(\\alpha)$ is a normal element in $\\GF{q^m}$. 

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: poly_basis = C.polynomial_basis()
			sage: C._is_normal_basis(poly_basis)
			Traceback (click to the left of this block for traceback)
			...
			ValueError: value of 'basis' keyword is not a normal basis
		"""	
		length = len(normal_basis)
		for i in range(length):
			if self.q_power(normal_basis[0],i)!=normal_basis[i]:
				raise ValueError("value of 'basis' keyword is not a normal basis")	

	def _trace(self,alpha):
		r"""
		Calculates the trace of an element $\\alpha \\in \\GF{q^m}$ of ``self``. 


		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: C._trace(tt)
			1
		"""	
		m = self._extension_degree
		trace = 0
		for i in range(m):
			trace = trace + self.q_power(alpha,i)
		return trace
	
	@cached_method
	def dual_basis(self , basis):
		r"""
		Returns a dual-basis $\\beta$ of a given basis $\\alpha$ of an extension field $\\GF{q^m}$ over $\\GF{q}$ of ``self``. 

		A basis $\\beta$ is a dual of a basis $\\alpha$ if and only if:
		
		.. MATH::

			\[
			trace(\alpha_i \beta_j) = \left\{ \begin{array}{lr}
			1, \ for \ i=j,&\\
			0, \ else.&
			\end{array}
			\right
			.\]

		INPUT:

			- ``basis`` -- basis of  $\\GF{q^m}$ over $\\GF{q}$

		OUTPUT:

			- ``dual_basis`` -- the dual basis of basis.

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: basis=C.polynomial_basis()
			sage: dual=C.dual_basis(basis);dual
			(tt^5 + tt^2 + 1, tt^5 + tt^4 + tt^2 + tt, tt^4 + tt)
			sage: C.dual_basis(dual)==basis
			True
		"""	
		m = self._extension_degree
		F = self._ground_field
		Fm = self._extension_field
		basis = vector(basis)
		entries = [self._trace(bi * bj) for bi in basis for bj in basis]
		B = matrix(Fm, m, entries).inverse()
		dual_basis = []
		dual_basis = [sum(x * y for x, y in zip(col, basis))
			      for col in B.columns()]
		self._is_dual_basis(basis, dual_basis)
		return vector(dual_basis)
		

	def _is_dual_basis(self, basis, dual_basis):
		r"""
		Checks if the given bases are dual of an extension_field $\\GF{q^m}$ over $\\GF{q}$ of ``self``. 

		INPUT:

			- ``basis`` -- basis of  $\\GF{q^m}$ over $\\GF{q}$.

			- ``dual_basis`` -- the dual basis of basis.

		OUTPUT:

			- raise an error if the given bases are not dual


		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: poly_basis = C.polynomial_basis()
			sage: dual_basis = C.dual_basis(poly_basis)
			sage: C._is_dual_basis(poly_basis,dual_basis)
			Traceback (click to the left of this block for traceback)
			...
			ValueError: value of 'basis' keyword and 'dual_basis' keyword are not
			dual

		"""
		m = self._extension_degree
		entries = [self._trace(betai * gammaj) for betai in basis for gammaj in dual_basis]
		I = matrix(m, entries)
		if I!=matrix.identity(m):
			raise ValueError("value of 'basis' keyword and 'dual_basis' keyword are not dual")

	@cached_method
	def _normal_dual_basis_matrix(self,normal_basis):
		r"""
		Construct the matrices $\\mathcal{B}$ and $\\mathcal{B^T}$ which are used to construct 
		the generetor and the parity-check matrices using a given normal basis. 

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: normal_basis = C.normal_basis()
			sage: B,B_dual=C._normal_dual_basis_matrix(normal_basis)

		"""
		n = len(normal_basis)
		dual_basis = self.dual_basis(normal_basis)
		B = matrix(n, n, lambda i, j: normal_basis[(i + j) % n])
		B_dual = matrix(n, n, lambda i, j: dual_basis[(i + j) % n])
		return B,B_dual

	def evaluation_points(self,basis=None):
		r"""
		Returns the points of $\\GF{q^m}$ in which the polynomials are evaluated.
		A basis of $\\GF{q^m}$ over $\\GF{q}$ could be given optionally in the input 'points'.

		The evaluation points are fixed elements $g_0,g_1,\\cdots,g_{n-1} \\in \\GF{q^m}$ 
		that are linearly independent over $\\GF{q}$, where n is the code length. 

		INPUT:

			- ``basis`` -- basis of  $\\GF{q^m}$ over $\\GF{q}$

		OUTPUT:

			- ``evaluation_points`` -- the first $n$ points in basis.

		
		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: C.evaluation_points()
			[1, tt, tt^2]
			sage: normal_basis = C.normal_basis();normal_basis
			(tt^4 + tt^2 + tt, tt^5 + tt^4 + tt^2, tt^5 + tt + 1)
			sage: C.evaluation_points(normal_basis)
			[tt^4 + tt^2 + tt, tt^5 + tt^4 + tt^2, tt^5 + tt + 1]

		"""	
		n = self.length()
		if basis is None:		
			basis = self.polynomial_basis()
		evaluation_points=[]		
		for i in range(n):
			evaluation_points.append(basis[i])					
		return vector(evaluation_points)
		
	def map_into_ground_field(self,vector):
		r"""
		Maps a vector $\\mathbf{\\textit{v}} \\in \\GF{q^m}^n$ into a matrix $\\mathbf{\\textit{A}} \\in \\GF{q}^{m \\times n}$ 
		where any element $\\mathbf{\\textit{vi}} \\in \\GF{q^m}$ is constituting a row in the matrix.
		
		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: poly_basis = C.evaluation_points()
			sage: C.map_into_ground_field(poly_basis)
			
			[1 0 0]
			[0 1 0]
			[0 0 1]

		"""	
		FE = self._relative_extension
		vector_length = len(vector)				
		for i in range(vector_length):
			if vector[i] not in self.extension_field():
            			raise ValueError("input should be an element of %s" % self.extension_field() )					
		vector_ground = []
		for i in range(vector_length):
    			 vector_ground.append(FE.relative_field_representation(vector[i]))	
		return matrix(vector_ground)

	def map_into_extension_field(self,matrix):
		r"""
		Maps a matrix $\\mathbf{\\textit{A}} \\in \\GF{q}^{m \\times n}$ into a vector $\\mathbf{\\textit{v}} \\in \\GF{q^m}^n$.
		
		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: poly_basis = C.evaluation_points()
			sage: poly_basis_matrix = C.map_into_ground_field(poly_basis)
			sage: C.map_into_extension_field(poly_basis_matrix) == poly_basis
			
			True
		"""	
		m = self._extension_degree
		FE = self._relative_extension
		F = self._ground_field
		V = VectorSpace(F,m)
		rows = matrix.nrows()	#len(matrix)
		for i in range(rows):
			if matrix[i] not in V:
            			raise ValueError("input should be an element of %s" % self.ground_field() )					
		matrix_extension = []
		for i in range(rows):
    			 matrix_extension.append(FE.absolute_field_representation(matrix[i]))	
		return matrix_extension

	def linear_independency_over_ground_field(self,basis):
		r"""
		Validates that a basis of $\\GF{q^m}$ over $\\GF{q}$ is linearly independent over $\\GF{q}$.
		
		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: basis = [tt,tt,tt]
			sage: C.linear_independency_over_ground_field(basis)

			Traceback (click to the left of this block for traceback)
			...
			ValueError: The elements provided are not linearly independent over
			Finite Field in t of size 2^2
		"""
		F = self.ground_field()
		m = self._extension_degree
		V = VectorSpace(F, m)
		basis_ground = self.map_into_ground_field(basis)
		if V.linear_dependence(basis_ground):
    			raise ValueError("The elements provided are not linearly independent over %s" % self.ground_field())	

	def frobenius_automorphism(self):
		r"""
		Defines the mapping  $\\Phi : \\GF{q^m}  \\rightarrow \\GF{q^m}$,  
		where $\\Phi(x)=x^q$ which maps an element $x \\in \\GF{q^m}$ over $\\GF{q}$ into $x^q$.
		
		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: Frob = C.frobenius_automorphism()
			sage: Frob(tt)

			tt^4
		"""
		return self._Frob

	def random_linearized_poly(self,dual_code = None):
		r"""
		Choose a random linearized polynomial with degree less than the dimension $(k)$ from 
		The set of all linearized polynomials over $\\GF{q^m}$ denoted by $\\mathcal{L}_{q^m}[x]$.

		A \emph{linearized polynomial} over $\\GF{q^m}$ is a polynomial of the form:  

		.. MATH::

			f(x)=\sum_{i=0}^{d} \alpha_ix^{[i]}, \quad \alpha_i \in \GF{q^m}, \alpha_d \neq 0

		In the case we want a message polynomial for the dual Gabidulin code, give the optional parameter dual_code = True

		INPUT:


			- ``dual_code`` -- an optional input if the random polynomial is from the dual code of self.

		OUTPUT:

			- ``linearized_poly`` -- a linearized polynomial $ \\in \\mathcal{L}_{q^m}[x]$ of degree less than the dimension.

		
		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: Frob = C.frobenius_automorphism()
			sage: L.<x>=Fm['x',Frob]
			sage: C.random_linearized_poly()
			(tt^4 + tt^3 + tt^2 + 1)*x + 1
			sage: C.random_linearized_poly(dual_code=True)
			tt^3 + 1
		"""
		k = self._dimension
		n = self._length
		linearized_poly_ring = self._linearized_poly_ring
		if dual_code:
			linearized_poly = linearized_poly_ring.random_element(degree=(0,n-k-1)) 
		else:
			linearized_poly = linearized_poly_ring.random_element(degree=(0,k-1))  
		return linearized_poly

	def _right_LEEA(self, a, b, d_stop):
		r"""
		Performs the right linearized extended Euclidean algorithm on the given polynomials $a(x)$ and $b(x)$ 
		where $deg_{q}(a(x)) \\geq  deg_{q}(b(x))$. 
		The algorithm have $a(x)$, $b(x)$ and the stop degree $d_{stop}$ as inputs and $r_{out}(x)$, 
		$v_{out}(x)$ and $u_{out}(x)$ as outputs, i.e.,


		.. MATH::
		
			r_{out}(x) =  v_{out}(x) \otimes a(x) + u_{out}(x) \otimes b(x),
		
		where $deg_{q}(r_{out})<d_{stop}$.

		INPUT:

			- ``a`` -- a linearized polynomial $ \\in \\mathcal{L}_{q^m}[x]$

			- ``b`` -- a linearized polynomial $ \\in \\mathcal{L}_{q^m}[x]$

			- ``d_stop`` -- the stopping degree

		OUTPUT:

			- ``r`` -- a linearized polynomial $ \\in \\mathcal{L}_{q^m}[x]$

			- ``u`` -- a linearized polynomial $ \\in \\mathcal{L}_{q^m}[x]$

			- ``v`` -- a linearized polynomial $ \\in \\mathcal{L}_{q^m}[x]$



		
		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: a=x^2+x; b=x^2; C._right_LEEA(a,b,2)
			(x, 1, 1)


	
		"""

		n = self.length()
		k = self.dimension()
		L = self._linearized_poly_ring
		r_last = a
		r = b
		u_last = L.zero()
		u = L.one()
		v_last = L.one()
		v = L.zero()
		while(r.degree() >= d_stop):
			(q , R) = r_last.right_quo_rem(r)
			(u , u_last) = (u_last - q * u , u)
			(v , v_last) = (v_last - q * v , v)
			(r , r_last) = (R,r)

		return r ,u ,v

	@cached_method
	def _lagrange_interpolating_polynomial(self, polynomial_coefficients, basis=None):
		r"""
		Let $(f_0,f_1,\\cdots,f_{n-1})$ be the coefficients of a linearized polynomial $f(x) \\in \\mathcal{L}_{q^m}[x]$ where $deg_{q}(f(x)) < n$.
		A linearized Lagrange interpolating polynomial denoted by $\\hat{f}(x)$ is the polynomial that pass through $n$ points 
		$\\{(u_0,f_0),(u_1,f_1),\\cdots,(u_{n-1},f_{n-1})\\}$, such that the following holds,
		
		.. MATH::
		
			\hat{f}(u_i)=f_i.

		INPUT:

			- ``polynomial_coefficients`` -- coefficients of a linearized polynomial $ \\in \\mathcal{L}_{q^m}[x]$

			- ``basis`` -- basis of  $\\GF{q^m}$ over $\\GF{q}$

		OUTPUT:

			- ``lagrange_interpolating_polynomial`` -- a lineairized polynomial that evaluates with the basis into polynomial_coefficients.



		EXAMPLES::


			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: c=vector([1, tt, tt^2]);c
			(1, tt, tt^2)	
			sage: basis=C.polynomial_basis(); evaluation=C.evaluation_points(basis)
			sage: c_hat=C._lagrange_interpolating_polynomial(c,basis)
			sage: C.evaluate_linearized_poly(c_hat,evaluation)
			(1, tt, tt^2)

		"""
		n = self.length()
		m = self._extension_degree
		k = self.dimension()
		L = self._linearized_poly_ring
		if basis is None:		
			basis = self.polynomial_basis()
		evaluation_points = self.evaluation_points(basis)

    		if not type(polynomial_coefficients)==list:
        		coefficients = polynomial_coefficients.list()	
	   	try:
			if not self._is_normal_basis(basis) and n.divides(m):		        
    				polynomial = L(coefficients)
                		lagrange_interpolating_polynomial = L(self.evaluate_linearized_poly(polynomial,evaluation_points).list())	        
	    	except ValueError:
			pairs = zip(evaluation_points, polynomial_coefficients);
			lagrange_interpolating_polynomial = L.lagrange_polynomial(pairs)
		
		return lagrange_interpolating_polynomial

	def evaluate_linearized_poly(self,linearized_poly=None,evaluation_points=None):
		r"""
		Given the ring of linearized polynomials $\\mathcal{L}_{q^m}[x]$, evaluation points(use self.evaluation_poits() if not given) 
		and a linearized polynomial(optional) this method evaluates the given polynomial at these points.

		INPUT:

			- ``linearized_poly`` -- linearized polynomial $ \\in \\mathcal{L}_{q^m}[x]$

			- ``evaluation points`` -- basis of  $\\GF{q^m}$ over $\\GF{q}$ of length $n$.

		OUTPUT:

			- ``evaluation`` -- the evaluation vector


		
		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: c=vector([1, tt, tt^2]);c
			(1, tt, tt^2)	
			sage: basis=C.polynomial_basis(); evaluation=C.evaluation_points(basis)
			sage: c_hat=C._lagrange_interpolating_polynomial(c,basis)
			sage: C.evaluate_linearized_poly(c_hat,evaluation)
			(1, tt, tt^2)
		"""
		k = self._dimension
		linearized_poly_ring = self._linearized_poly_ring
		if linearized_poly is None:		
			linearized_poly = self.random_linearized_poly(linearized_poly_ring)
		if evaluation_points is None:		
			evaluation_points = self.evaluation_points() 	
		evaluation = linearized_poly.multi_point_evaluation(evaluation_points)
		return vector(evaluation)


	def q_power(self,field_element,exponent):
		r"""
		Given an element $\\alpha \\in \\GF{q^m}$ and an exponent $i$, it outputs the $q$-power
		$\\alpha^{[i]} = \\alpha^{q^i}$.

		INPUT:

			- ``field_element`` -- an element  $ \\alpha \\in \\GF{q^m}$

			- ``exponet`` -- an integer number

		OUTPUT:

			- ``result`` -- the $i^{th}$ $q$-power of field element, where $i$ is equal to the exponent value.
 
		
		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: C.q_power(tt,0)

			tt
		"""
		F = self._ground_field
		Fm = self._extension_field
		q = F.order()
		Fm_degree = Fm.degree()
		result = field_element**(q**(exponent % Fm_degree))

		return result

	def code_space(self):
		r"""
		Returns the Code vector space of `self`.

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: C.code_space()
		    
			Vector space of dimension 3 over Finite Field in tt of size 2^6

		"""
		return VectorSpace(self.extension_field(),self.length())

	def _create_generator_matrix(self,evaluation_points,k):
		n = self._length
		Fm = self._extension_field 
		G = matrix(Fm, k, n, lambda i,j: self.q_power(evaluation_points[j] , i))
		return G

    	@cached_method
    	def generator_matrix(self,basis=None):
		r"""
		Defines the Generator matrix of a gabidulin code $Gab[n,k]$. 

		A \emph{Generator matrix} of a $Gab[n,k]$ code is the $n \\times k$ matrix:

		.. MATH::

			\[
			\mathbf{G} = \left( \begin{array}{lllllllllllllll}
			g_{0}^{[0]}&g_{1}^{[0]}&\cdots &g_{n-1}^{[0]} \\
			g_{0}^{[1]}&g_{1}^{[1]}&\cdots &g_{n-1}^{[1]} \\
			\vdots & \vdots & \ddots & \vdots\\
			g_{0}^{[k-1]}&g_{1}^{[k-1]}&\cdots &g_{n-1}^{[k-1]}
			\end{array}
			\right)
			.\]

		INPUT:


			- ``basis`` -- basis of  $\\GF{q^m}$ over $\\GF{q}$

		OUTPUT:

			- ``G`` -- Generator matrix of $Gab[n,k]$


		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: C.generator_matrix()

			[                          1                          tt                        tt^2]
			[                          1                        tt^4 tt^5 + tt^4 + tt^2 + tt + 1]
			sage: normal_basis = C.normal_basis()
			sage: C.generator_matrix(normal_basis)
			[tt^5 + tt^2 + tt             tt^5    tt^2 + tt + 1]
			[            tt^5    tt^2 + tt + 1 tt^5 + tt^2 + tt]

		"""
		Frob = self._Frob
		k = self.dimension()
		n = self.length()
		m = self.extension_degree()
		Fm = self.extension_field()
	    	if basis is None:		
			basis = self.polynomial_basis()
		if not len(basis) == m :
            		raise ValueError("length of the basis must be %d" %  m )
	   	try:
			if not self._is_normal_basis(basis):		        
		    		G=self._normal_dual_basis_matrix(basis)[1][:,0:k].transpose()        
	    	except ValueError:
			evaluation_points = self.evaluation_points(basis)  
		    	G = self._create_generator_matrix(evaluation_points,k)  
		
        	#G.set_immutable()
        	return G

    	@cached_method
    	def parity_check_matrix(self,basis=None):
		r"""
		Defines the Parity-Check matrix of a gabidulin code $Gab[n,k]$. 

		Let $\\mathbf{G}$ be a generator matrix of a $Gab[n,k]$ and $g_0,g_1,\\cdots,g_{n-1} \\in \\GF{q^m}$ are linearly independent over $\\GF{q}$.
		A \emph{Parity-Check matrix} denoted by $\\mathbf{H}$ where $\\mathbf{G} \\cdot \\mathbf{H}^T = \\mathbf{0}$ is the $n \\times k$ matrix:

		.. MATH::

			\[
			\mathbf{H} = \left( \begin{array}{lllllllllllllll}
			h_{0}^{[0]}&h_{1}^{[0]}&\cdots &h_{n-1}^{[0]} \\
			h_{0}^{[1]}&h_{1}^{[1]}&\cdots &h_{n-1}^{[1]} \\
			\vdots & \vdots & \ddots & \vdots\\
			h_{0}^{[n-k-1]}&h_{1}^{[n-k-1]}&\cdots &h_{n-1}^{[n-k-1]}
			\end{array}
			\right)
			,\]
		where $h_0,h_1,\\cdots,h_{n-1}$ are non-zero solution of the equations:

		.. MATH::
		
			\sum_{i=0}^{n-1}g_i^{[j]}h_i \qquad \forall j \in [-n+k+1,k-1]. 

		INPUT:


			- ``basis`` -- basis of  $\\GF{q^m}$ over $\\GF{q}$

		OUTPUT:

			- ``H`` -- parity check matrix of $ Gab[n,k]$

		
		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: C.parity_check_matrix()

			[                     1 tt^5 + tt^4 + tt^2 + 1            tt^3 + tt^2]
			sage: normal_basis = C.normal_basis()
			sage: C.parity_check_matrix(normal_basis)
			[tt^5 + tt^2 + tt             tt^5    tt^2 + tt + 1]
		"""
		Frob = self._Frob
		k = self.dimension()
		n = self.length()
		m = self.extension_degree()
		Fm = self.extension_field()
		F = self.ground_field()
		q=F.order()		
	    	if basis is None:		
			basis = self.polynomial_basis()
		if not len(basis) == m :
            		raise ValueError("length of the basis must be %d" %  m )
    		try:
        		if not self._is_normal_basis(basis):		        
            			H=self._normal_dual_basis_matrix(basis)[0][k:,:]        
    		except ValueError:      
			evaluation_points = self.evaluation_points(basis)#here there was no basis between paranthesis
			coefficient_matrix = matrix(Fm, n - 1, n, lambda i,j: self.q_power(evaluation_points[j] , -n + k + 1 + i))
			solution_space = coefficient_matrix.right_kernel()
			parity_matrix_space = solution_space.basis() 
			parity_points =  vector(parity_matrix_space[0])				
			H = self._create_generator_matrix(parity_points,n-k)    
	
        	#H.set_immutable()
		return H

		
	@cached_method
	def dual_code(self):
		r"""
		Defines the dual code of the given Gabidulin code of ``self``. 

		Let $Gab[n,k]$ be a Gabidulin code and $\\mathbf{\\textit{c}} \\in Gab[n,k]$ be any codeword in the code. 
		The dual code $Gab[n,k]^{\\perp}$ is the Gabidulin code $Gab[n,n-k]$ that is defined by,


		.. MATH::

			Gab[n,k]^{\perp} = \{ c^{\perp} \in \GF{q^m}^n | \langle c^{\perp} , c \rangle = 0, \quad \forall c \in Gab[n,k] \} .


		OUTPUT:

			- ``C_dual`` -- the dual code $Gab[n,n-k]$

		
		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: C
			Gabidulin Code Gab[3,2] over Finite Field in tt of size 2^6
			sage: C.dual_code()
			Gabidulin Code Gab[3,1] over Finite Field in tt of size 2^6

		"""
		
		F = self._ground_field
		Fm = self._extension_field
		k = self._dimension
		n = self._length
		L = self._linearized_poly_ring
		C_dual = GabidulinCode(F,Fm,L,n,n-k)
		return C_dual

	def _repr_(self):    
	        return "Gabidulin Code Gab[%s,%s] over %s" % (self.length(), self.dimension(), self.extension_field())

    	def _latex_(self):
        	return "\\textnormal{Gabidulin Code Gab}[%s,%s] \\textnormal{over }%s" % (self.length(), self.dimension(), self.extension_field())
	
    	def __eq__(self, other):
        	return isinstance(other, GabidulinCode)\
               		and self.length() == other.length()\
                	and self.dimension() == other.dimension()\
			and self.ground_field() == other.ground_field()\
			and self.extension_field() == other.extension_field()\


####################### encoders ###############################

class GabidulinCodeGeneratorMatrixEncoder(Encoder):
	r"""
	Defines the encoding of a Gabidulin code $Gab[n,k]$ using the generator matrix and an information vector. 

	Let $f(x)$ be a linearized polynomial with degree less than the dimension $(k)$ from the set of all linearized polynomials
	over $\\GF{q^m}$ denoted by $\\mathcal{L}_{q^m}[x]$ and $\\mathbf{\\textit{f}}$ be a vector represents the coefficients of $f(x)$. 
	The encoding of a $Gab[n,k]$ using a generator matrix $\\mathbf{G}$:

	.. MATH::

		Gab[n,k] = \{ \mathbf{\textit{c}} \in \GF{q^m}^n  | \quad \mathbf{\textit{c}} = \mathbf{\textit{f}} \cdot \mathbf{\textit{G}}, \quad 
		\forall \mathbf{\textit{f}} \in \GF{q^m}^k \}.

	Such that, an information vector $\\mathbf{\\textit{f}}$ is mapped into a codeword $\\mathbf{\\textit{c}}=\\mathbf{\\textit{f}} \\cdot \\mathbf{\\textit{G}}$ 
	using the following mapping:

	.. MATH::

		\mathbf{\textit{f}} \mapsto \mathbf{\textit{f}} \cdot \mathbf{\textit{G}}.

	EXAMPLES::

		sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
		sage: F.<t> = GF(4)
		sage: Fm.<tt> = GF(4^3)
		sage: n=3
		sage: k=2
		sage: q = F.order()
		sage: p = F.characteristic()
		sage: Frob = Fm.frobenius_endomorphism(log(q,p))
		sage: L.<x>=Fm['x',Frob]
		sage: C=GabidulinCode(F,Fm,L,n,k)
		sage: p=C.random_linearized_poly()
		sage: G = C.generator_matrix()
		sage: E1=C.encoder("GeneratorEncoder")
		sage: c1=E1.encode(G,p);c1

		(tt^5 + tt^3 + tt + 1, tt^5 + tt^3 + tt^2 + tt + 1, tt^4)
	"""

   	def __init__(self, code):
      		super(GabidulinCodeGeneratorMatrixEncoder, self).__init__(code) 

	def __eq__(self, other):
		return isinstance(other, GabidulinCodeGeneratorMatrixEncoder)\
                	and self.code() == other.code()\

	def _latex_(self):
        	return "\\textnormal{Generator matrix based encoder for }%s" % self.code()._latex_()

	def _repr_(self):
		return "Generator matrix based encoder for %s" % self.code()

	def _is_codeword(self,codeword,basis=None):
		r"""
		Return True if the given codeword is a valid codeword of ``self`` code.

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: p=C.random_linearized_poly()
			sage: G = C.generator_matrix()
			sage: E1=C.encoder("GeneratorEncoder")
			sage: c1=E1.encode(G,p)
			sage: E1._is_codeword(c1)
			True

		
		"""
		C = self.code()
		H = C.parity_check_matrix(basis)
		Code = H.right_kernel()
	    	if basis is None:		
			basis = C.polynomial_basis()
		if codeword in Code:
			return True
		else:
			return False

	def encode(self,Generator,linearized_poly):
		r"""
		Return a codeword of ``self`` code.

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: p=C.random_linearized_poly()
			sage: G = C.generator_matrix()
			sage: E1=C.encoder("GeneratorEncoder")
			sage: c1=E1.encode(G,p);c1
			sage: E1._is_codeword(c1)
			(tt^5 + tt^3 + tt + 1, tt^5 + tt^3 + tt^2 + tt + 1, tt^4)
		
		"""

		C = self.code()
		k = C.dimension()
		degree = linearized_poly.degree()
		len_linearized_poly = len((vector(linearized_poly)))
		vector_linearized_poly = []
		for i in range(len_linearized_poly):
			vector_linearized_poly.append(vector(linearized_poly)[i])
		for i in range(k-degree-1):
			vector_linearized_poly.append(0)
		codeword = vector(vector_linearized_poly) * Generator
		return codeword

	def message_space(self):
		r"""
		Return the message space of ``self``

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: E1=C.encoder("GeneratorEncoder")
			sage: E1.message_space()
			Skew Polynomial Ring in x over Finite Field in tt of size 2^6 twisted by
			tt |--> tt^(2^2)		
		
		"""

		C = self.code()
		return C.linearized_poly_ring()
		

class GabidulinCodePolynomialEvaluationEncoder(Encoder):

	r"""
	Defines the encoding of a Gabidulin code $Gab[n,k]$ using evaluation of a linearized polynomial at fixed points. 

	An $[n,k]$ Gabidulin $Gab[n,k]$ is a linear MRD code that consists of all words (vectors) of the form $(f(g_0),f(g_1),\\cdots,f(g_{n-1}))$, 
	where the fixed elements $g_0,g_1,\\cdots,g_{n-1} \\in \\GF{q^m}$ are linearly independent over $\\GF{q}$ (referred to as the evaluation points) 
	and $f(x)$ include all linearized polynomials over $\\GF{q^m}$ of degree less than k:

	.. MATH::

		Gab[n,k] = \{ (f(g_0),f(g_1),\cdots,f(g_{n-1})) | \quad deg_{q}(f(x))< k \}.


	EXAMPLES::

		sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
		sage: F.<t> = GF(4)
		sage: Fm.<tt> = GF(4^3)
		sage: n=3
		sage: k=2
		sage: q = F.order()
		sage: p = F.characteristic()
		sage: Frob = Fm.frobenius_endomorphism(log(q,p))
		sage: L.<x>=Fm['x',Frob]
		sage: C=GabidulinCode(F,Fm,L,n,k)
		sage: p=C.random_linearized_poly()
		sage: basis=C.polynomial_basis()
		sage: E2=C.encoder("EvaluationEncoder")
		sage: c2=E2.encode(basis,p);c2

		(tt^5 + tt^3 + tt + 1, tt^5 + tt^3 + tt^2 + tt + 1, tt^4)
	"""
   	def __init__(self, code):
      		super(GabidulinCodePolynomialEvaluationEncoder, self).__init__(code)

	def __eq__(self, other):
		return isinstance(other, GabidulinCodePolynomialEvaluationEncoder)\
                	and self.code() == other.code()
    	def _repr_(self):
        	return "Polynomial evaluation based encoder for %s" % self.code()
	def _latex_(self):
        	return "\\textnormal{Polynomial evaluation based encoder for }%s" % self.code()._latex_()

	def _is_codeword(self,codeword,basis=None):
		r"""
		Return True if the given codeword is a valid codeword of ``self`` code.

		INPUT:

			- ``codeword`` -- codeword vector $\\in Gab[n,k]$

			- ``basis`` -- basis of  $\\GF{q^m}$ over $\\GF{q}$

		OUTPUT:

			- ``True`` -- if the given codeword $\\in Gab[n,k]$ is a valid codeword.


		EXAMPLES::


			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: p=C.random_linearized_poly()
			sage: basis=C.polynomial_basis()
			sage: E2=C.encoder("EvaluationEncoder")
			sage: c2=E2.encode(basis,p);c2
			sage: E2._is_codeword(c2)
			True
		
		"""

		C = self.code()
		H = C.parity_check_matrix(basis)
		Code = H.right_kernel()
		if codeword in Code:
			return True
		else:
			return False

	def encode(self,linearized_poly,basis=None):
		r"""
		Return a codeword of ``self`` code.

		INPUT:

			- ``linearized_poly`` -- linearized polynomial $ \\in \\mathcal{L}_{q^m}[x]$

			- ``basis`` -- basis of  $\\GF{q^m}$ over $\\GF{q}$

		OUTPUT:

			- ``codeword`` -- encoded codeword $\\in Gab[n,k]$

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: p=C.random_linearized_poly()
			sage: basis=C.polynomial_basis()
			sage: E2=C.encoder("EvaluationEncoder")
			sage: c2=E2.encode(basis,p);c2
			(tt^5 + tt^3 + tt + 1, tt^5 + tt^3 + tt^2 + tt + 1, tt^4)

		"""

		C = self.code()
		k = C.dimension()
		degree = linearized_poly.degree()
		if basis is None:		
			basis = C.polynomial_basis()
	   	try:
			if not C._is_normal_basis(basis):		        
		    		dual_basis=C.dual_basis(basis)  
                                evaluation_points = C.evaluation_points(dual_basis)     
	    	except ValueError:
			evaluation_points = C.evaluation_points(basis)  
		if not degree < k:
			raise ValueError("degree of linearized polynomial must be less than k = %d" %  k )
		codeword = C.evaluate_linearized_poly(linearized_poly,evaluation_points)
		return vector(codeword)

    	def unencode_nocheck(self, codeword, basis=None):
		r"""
		Return the message polynomial of the given codeword.

		This method does not check if the given codeword is a valid codeword.


		INPUT:

			- ``codeword`` -- codeword vector $\\in \\GF{q^m}^n$

			- ``basis`` -- basis of  $\\GF{q^m}$ over $\\GF{q}$

		OUTPUT:

			- ``p`` -- linearized polynomial $p \\in \\mathcal{L}_{q^m}[x]$



		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: p=C.random_linearized_poly()
			sage: basis=C.polynomial_basis()
			sage: E2=C.encoder("EvaluationEncoder")
			sage: c2=E2.encode(basis,p);
			sage: p_estimated=E2.unencode_nocheck(c2,basis)
			sage: p_estimated==p
			True

		"""

		C = self.code()
		L = self.message_space()
		if basis is None:		
			basis = C.polynomial_basis()
		p = C._lagrange_interpolating_polynomial(codeword,basis)
		return p


	def message_space(self):
		r"""
		Return the message space of ``self``



		OUTPUT:

			- ``L`` -- the linearized polynomial ring $\\mathcal{L}_{q^m}[x]$

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: E2=C.encoder("EvaluationEncoder")
			sage: E2.message_space()
			Skew Polynomial Ring in x over Finite Field in tt of size 2^6 twisted by
			tt |--> tt^(2^2)		
		
		"""

		C = self.code()
		L = C.linearized_poly_ring()
		return L
	
		


####################### decoders ###############################

class GabidulinCodeGaoDecoder(Decoder):
	r"""
	The Gao-like Gabidulin decoder is a (transformed) key-equation-based algorithm that directly gives the decoding result in one step,
	as analogous to Gao's decoder for Reed-Solomon codes. 

	In order to decode a codeword the Gao-like algorithm uses the following key equation,

	.. MATH::

    		\Lambda(x) \otimes f(x) =  \Omega(x) \otimes M_{\mathcal{G}}(x) + \Lambda(x) \otimes \hat{r}(x).

	where $\\mathcal{G}=\\{g_0,g_1,\\cdots,g_{n-1}\\}$ is a basis over $\\GF{q}$ that is used as evaluation points of $Gab[n,k]$, $r(x)$ is the received word polynmial
	such that $\\hat{r}(x)$ is its transformed polynomial, $M_{\\mathcal{G}}(x)$ is the minimal subspace polynomial, $\\Omega(x) \\in \\mathcal{L}_{q^m}[x]$ is a linearized 
	polynomial over $\\GF{q^m}$, $\\Lambda(x)$ is the error span polynomial and $f(x)$ is the message polynmial. The degree constraints is as follows, 
	$deg_{q}(M_{\\mathcal{G}}(x)) = n$, $deg_{q}(\\hat{r}(x)) < n$, $deg_{q}(\\Lambda(x)) = t \\leq \\lfloor {(d-1)}/{2} \\rfloor 
	= \\lfloor {(n-k)}/{2} \\rfloor$ and $deg_{q}(f(x)) < k$. 

	INPUT:

	- ``code`` -- the Gabidulin code that will be decoded.

	EXAMPLES::

		sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
		sage: F.<t> = GF(4)
		sage: Fm.<tt> = GF(4^3)
		sage: n=3
		sage: k=2
		sage: q = F.order()
		sage: p = F.characteristic()
		sage: Frob = Fm.frobenius_endomorphism(log(q,p))
		sage: L.<x>=Fm['x',Frob]
		sage: C=GabidulinCode(F,Fm,L,n,k)
		sage: D=C.decoder("GabidulinGao")
		sage: D
		Gao-like decoder for the Gabidulin Code Gab[3,2] over Finite Field 
		in tt of size 2^6

	"""

	def __init__(self, code):
		
		if not isinstance(code, GabidulinCode):
			raise ValueError("The code given as input is not a Gabidulin code")
		super(GabidulinCodeGaoDecoder, self).__init__(code, code.code_space(),"EvaluationEncoder")


	def _repr_(self):

		return "Gao-like decoder for %s" % self.code()


	def _latex_(self):
		return "\\textnormal{Gao-like decoder for }%s" % self.code()._latex_()


	def __eq__(self, other):
		return (isinstance(other, GabidulinCodeGaoDecoder)
			and self.code() == other.code())

		
	@cached_method
	def _minimal_subspace_polynomial(self,basis=None):
		r"""
		Return the minimal subspace polynomial $M_{\\mathcal{U}}(x)$ of the given basis $\\mathcal{U}=(u_0,u_1,\\cdots,u_{n-1}) \\in \\GF{q^m}$.
 
		A minimal subspace polynomial is the linearized polynomial with least degree such that it evaluates to zero at all basis elements, i.e.,

		.. MATH::
		
			M_{\mathcal{U}}(x) = \prod_{i = 1}^{n-1}(x - u_i).


		INPUT:

			- ``basis`` -- basis of  $\\GF{q^m}$ over $\\GF{q}$

		OUTPUT:

			- ``M`` -- Minimal subspace polynomial of the given basis.
		EXAMPLES::


			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^3)
			sage: n=3
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: D=C.decoder("GabidulinGao")
			sage: D._minimal_subspace_polynomial()
			x^3 + 1
		
		"""
		C = self.code()
		E = self.connected_encoder()
		n, m = C.length(), C.extension_degree()
		L = E.message_space()
		x = L.gen()
		if basis is None:		
			basis = C.polynomial_basis()
		evaluation_points = C.evaluation_points(basis)
		
		if n==m:
			M = x**m-L.one()
		else:
		   	try:
				if not C._is_normal_basis(basis) and n.divides(m):
					M = x**n-L.one()
		   	except ValueError:
				M = L.minimal_vanishing_polynomial(evaluation_points)

		return M

	@cached_method
	def decode_to_code(self, received_word, basis=None):
		r"""
		Decode a received word into a codeword.

		This decoder find the unique error word $\\mathbf{\\textit{e}}=\\mathbf{\\textit{r}}-\\mathbf{\\textit{c}}$ such that $wt_{rk}(\\mathbf{\\textit{e}}) = t
		\\leq \\frac{d-1}{2}$ where $\\mathbf{\\textit{r}}$ is the received word and $\\mathbf{\\textit{c}}$ is the transmitted codeword.


		INPUT:

			- ``received_word`` -- the received word $\\in \\GF{q^m}^n$

			- ``basis`` -- basis of  $\\GF{q^m}$ over $\\GF{q}$

		OUTPUT:

			- ``estimated_codeword`` -- estimated codeword $\\in Gab[n,k]$

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^4)
			sage: n=4
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: E=C.encoder("EvaluationEncoder")
			sage: D=C.decoder("GabidulinGao")
			sage: t = (1,D.decoding_radius())
			sage: V = C.code_space();
			sage: Chan = channels.StaticErrorRateChannel(V, t)
			sage: message_polynomial = x^1+tt;message_polynomial
			x + tt
			sage: basis = C.polynomial_basis()
			sage: codeword=E.encode(message_polynomial,basis)
			sage: received_word=Chan(codeword)
			sage: estimated_codeword = D.decode_to_code(received_word,basis
			sage: estimated_codeword == codeword
			True



		"""
		C = self.code()
		E = self.connected_encoder()

		if basis is None:
			basis = C.polynomial_basis()

		if E._is_codeword(received_word,basis):
			return received_word

		estimated_message = self.decode_to_message(received_word,basis)
		estimated_codeword = E.encode(estimated_message,basis)

		if not E._is_codeword(estimated_codeword,basis):
			raise DecodingError("Decoding failed because the decoded word is not a codeword of the code")

		return estimated_codeword

	@cached_method
	def decode_to_message(self, received_word, basis=None):
		r"""
		Decode a received word into a message polynomial



		INPUT:

			- ``received_word`` -- the received word $\\in \\GF{q^m}^n$

		OUTPUT:

			- ``p`` -- estimeted message polynomial $\\in \\mathcal{L}_{q^m}[x]$

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^4)
			sage: n=4
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: E=C.encoder("EvaluationEncoder")
			sage: D=C.decoder("GabidulinGao")
			sage: t = (1,D.decoding_radius())
			sage: V = C.code_space();
			sage: Chan = channels.StaticErrorRateChannel(V, t)
			sage: message_polynomial = x^1+tt;message_polynomial
			x + tt
			sage: basis = C.polynomial_basis()
			sage: codeword=E.encode(message_polynomial,basis)
			sage: received_word=Chan(codeword)
			sage: estimated_message = D.decode_to_message(received_word,basis)
			sage: estimated_message == message_polynomial
			True



		"""
		C = self.code()
		E = self.connected_encoder()
		n, k = C.length(), C.dimension()
		L = E.message_space()

		if received_word not in C.code_space():
			raise ValueError("The word does not belong to the code-space")

		if basis is None:
			basis = C.polynomial_basis()

		lagrange_interpolating_polynomial = C._lagrange_interpolating_polynomial(received_word,basis)
		M = self._minimal_subspace_polynomial(basis)
		d_stop = (k + n) // 2
		(r_out, u_out, v_out) = C._right_LEEA(M, lagrange_interpolating_polynomial,d_stop)
		(estimated_message, r) = r_out.left_quo_rem(u_out)

		if not r.is_zero():
			raise DecodingError("Decoding failure, as the number of corrupted positions is larger than floor({d-1}/{2}) = %d of the %s"\
				% (self.decoding_radius(),C))

		if estimated_message not in L:
			raise DecodingError("Decoding failure, because the decoded message is not a valid message")

		return estimated_message


	def decoding_radius(self):
		r"""
		Return the decoding radius of the decoder, 

		OUTPUT:

			- ``t_max`` -- maximum number of guranteed decodable errors $=\\lfloor {(n-k)}/{2} \\rfloor$

		EXAMPLES::

			sage: load("/home/maeahmed/Gabidulin sage/Gabidulin_code.py")
			sage: F.<t> = GF(4)
			sage: Fm.<tt> = GF(4^4)
			sage: n=4
			sage: k=2
			sage: q = F.order()
			sage: p = F.characteristic()
			sage: Frob = Fm.frobenius_endomorphism(log(q,p))
			sage: L.<x>=Fm['x',Frob]
			sage: C=GabidulinCode(F,Fm,L,n,k)
			sage: E=C.encoder("EvaluationEncoder")
			sage: D=C.decoder("GabidulinGao")
			sage: D.decoding_radius()
			1
	
		"""
		C = self.code()
		t_max = (C.minimum_distance() - 1) // 2
		return t_max





####################### registration ###############################

GabidulinCode._registered_encoders["GeneratorEncoder"] = GabidulinCodeGeneratorMatrixEncoder
GabidulinCode._registered_encoders["EvaluationEncoder"] = GabidulinCodePolynomialEvaluationEncoder
GabidulinCode._registered_decoders["GabidulinGao"] = GabidulinCodeGaoDecoder


 
