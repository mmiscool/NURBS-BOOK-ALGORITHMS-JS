//----------------Chapter 1 : Curve and Surface Basics 

// ALGORITHM A1.1
// Horner's algorithm for computing a point on a power basis curve.
function Horner1(a, n, u0) {
    let C = a[n];
    for (let i = n - 1; i >= 0; i--) {
        C = C * u0 + a[i];
    }
    return C;
}

// Example usage of ALGORITHM A1.1
// let a = [/* coefficients array */];
// let n = a.length - 1;
// let u0 = /* value of u */;
// let point = Horner1(a, n, u0);
// console.log(point);


// ALGORITHM A1.2
// Bernstein's algorithm for computing the value of a Bernstein polynomial.
function Bernstein(i, n, u) {
    let temp = new Array(n).fill(0.0);
    temp[n - i] = 1.0;
    let u1 = 1.0 - u;

    for (let k = 1; k <= n; k++) {
        for (let j = n; j >= k; j--) {
            temp[j] = u1 * temp[j] + u * temp[j - 1];
        }
    }
    return temp[n];
}

// Example usage of ALGORITHM A1.2
// let i = /* index */;
// let n = /* degree */;
// let u = /* value of u */;
// let B = Bernstein(i, n, u);
// console.log(B);


// ALGORITHM A1.3
// Algorithm for computing all nth-degree Bernstein polynomials.
function AllBernstein(n, u) {
    let B = new Array(n + 1).fill(0.0);
    B[0] = 1.0;
    let u1 = 1.0 - u;

    for (let j = 1; j <= n; j++) {
        let saved = 0.0;
        for (let k = 0; k < j; k++) {
            let temp = B[k];
            B[k] = saved + u1 * temp;
            saved = u * temp;
        }
        B[j] = saved;
    }
    return B;
}

// Example usage of ALGORITHM A1.3
// let n = /* degree */;
// let u = /* value of u */;
// let Bs = AllBernstein(n, u);
// console.log(Bs);




// ALGORITHM A1.4
// Function to compute a point on a Bezier curve using Bernstein polynomials.
function PointOnBezierCurve(P, n, u) {
    // Compute point on Bezier curve.
    // Input: P (control points), n, u
    // Output: C (a point)

    let B = AllBernstein(n, u); // B is calculated using the previously defined AllBernstein function
    let C = 0.0;

    for (let k = 0; k <= n; k++) {
        C = C + B[k] * P[k];
    }
    return C;
}

// Example usage of ALGORITHM A1.4
// let P = [/* array of control points */];
// let n = P.length - 1;
// let u = /* value of u */;
// let pointOnCurve = PointOnBezierCurve(P, n, u);
// console.log(pointOnCurve);



// ALGORITHM A1.5
// Function to compute a point on a Bezier curve using de Casteljau's algorithm.
function deCasteljau1(P, n, u) {
    // Compute point on a Bézier curve using de Casteljau.
    // Input: P (control points), n, u
    // Output: C (a point)

    let Q = P.slice(); // Use local array so we do not destroy control points

    for (let k = 1; k <= n; k++) {
        for (let i = 0; i <= n - k; i++) {
            Q[i] = (1.0 - u) * Q[i] + u * Q[i + 1];
        }
    }

    return Q[0];
}

// Example usage of ALGORITHM A1.5
// let P = [/* array of control points */];
// let n = P.length - 1;
// let u = /* value of u */;
// let pointOnCurve = deCasteljau1(P, n, u);
// console.log(pointOnCurve);








// ALGORITHM A1.6
// Function to compute a point on a power basis surface.
function Horner2(a, n, m, u0, v0) {
    // Compute point on a power basis surface.
    // Input: a (array of arrays), n, m, u0, v0
    // Output: S

    let S = new Array(m + 1).fill(0);
    for (let i = 0; i <= n; i++) {
        S = Horner1(a[i], m, v0, S); // a[i] is the ith row
    }
    return Horner1(S, n, u0);
}

// Example usage of ALGORITHM A1.6
// let a = [/* array of arrays representing the surface control points */];
// let n = /* the degree in the u direction */;
// let m = /* the degree in the v direction */;
// let u0 = /* value of u */;
// let v0 = /* value of v */;
// let surfacePoint = Horner2(a, n, m, u0, v0);
// console.log(surfacePoint);






// ALGORITHM A1.7
// Function to compute a point on a Bézier surface using de Casteljau's algorithm.
function deCasteljau2(P, n, m, u0, v0) {
    // Compute a point on a Bézier surface by the de Casteljau.
    // Input: P (array of arrays of control points), n, m, u0, v0
    // Output: S (a point)

    let S;
    let Q = [];

    if (n <= m) {
        for (let j = 0; j <= m; j++) {
            Q[j] = deCasteljau1(P.map(row => row[j]), n, u0); // P[j] is the jth column
        }
        S = deCasteljau1(Q, m, v0);
    } else {
        for (let i = 0; i <= n; i++) {
            Q[i] = deCasteljau1(P[i], m, v0); // P[i] is the ith row
        }
        S = deCasteljau1(Q, n, u0);
    }

    return S;
}

// Example usage of ALGORITHM A1.7
// let P = [/* array of arrays representing the surface control points */];
// let n = /* the degree in the u direction */;
// let m = /* the degree in the v direction */;
// let u0 = /* value of u */;
// let v0 = /* value of v */;
// let surfacePoint = deCasteljau2(P, n, m, u0, v0);
// console.log(surfacePoint);












//--------------------Chapter 2 : B-Spline Basis Functions 


// ALGORITHM A2.1
// Function to determine the knot span index in NURBS calculations.
function FindSpan(n, p, u, U) {
    // Determine the knot span index
    // Input: n (number of knots minus one), p (degree of B-spline), u (parameter value), U (knot vector)
    // Return: the knot span index

    if (u === U[n + 1]) return n; // Special case

    let low = p;
    let high = n + 1;
    let mid = Math.floor((low + high) / 2);

    while (u < U[mid] || u >= U[mid + 1]) {
        if (u < U[mid]) {
            high = mid;
        } else {
            low = mid;
        }
        mid = Math.floor((low + high) / 2);
    }

    return mid;
}

// Example usage of ALGORITHM A2.1
// let n = /* the number of knots minus one */;
// let p = /* the degree of the B-spline */;
// let u = /* the parameter value */;
// let U = [/* the knot vector */];
// let span = FindSpan(n, p, u, U);
// console.log(span); // This will output the knot span index







// ALGORITHM A2.2
// Function to compute the nonvanishing basis functions.
function BasisFuns(i, p, u, U) {
    // Compute the nonvanishing basis functions
    // Input: i (knot span), p (degree of B-spline), u (parameter value), U (knot vector)
    // Output: N (array of basis functions)

    let N = new Array(p + 1).fill(0.0);
    N[0] = 1.0;
    let left = new Array(p + 1);
    let right = new Array(p + 1);

    for (let j = 1; j <= p; j++) {
        left[j] = u - U[i + 1 - j];
        right[j] = U[i + j] - u;
        let saved = 0.0;

        for (let r = 0; r < j; r++) {
            let temp = N[r] / (right[r + 1] + left[j - r]);
            N[r] = saved + right[r + 1] * temp;
            saved = left[j - r] * temp;
        }
        N[j] = saved;
    }

    return N;
}

// Example usage of ALGORITHM A2.2
// let i = /* the knot span */;
// let p = /* the degree of the B-spline */;
// let u = /* the parameter value */;
// let U = [/* the knot vector */];
// let basisFuns = BasisFuns(i, p, u, U);
// console.log(basisFuns); // This will output the array of basis functions






// Function to find the span and multiplicity of a knot in a knot vector
function findSpanMult(n, p, u, UP) {
    // Input: n (number of control points minus 1), p (degree of curve), u (parameter value),
    //        UP (knot vector)
    // Output: span (the span in which u lies), mult (multiplicity of u)

    if (u === UP[n + 1]) {
        return [n, 1]; // Special case when u is the last knot value
    }

    // Find the span of u
    let low = p;
    let high = n + 1;
    let mid = Math.floor((low + high) / 2);
    while (u < UP[mid] || u >= UP[mid + 1]) {
        if (u < UP[mid]) {
            high = mid;
        } else {
            low = mid;
        }
        mid = Math.floor((low + high) / 2);
    }

    // Find the multiplicity of u
    let mult = 0;
    for (let i = mid; i < UP.length && UP[i] === u; i++) {
        mult++;
    }

    return [mid, mult];
}

// Example usage of findSpanMult
// let n = /* number of control points minus 1 */;
// let p = /* degree of curve */;
// let u = /* parameter value */;
// let UP = [/* knot vector */];
// let [span, mult] = findSpanMult(n, p, u, UP);
// console.log('Span:', span, 'Multiplicity:', mult);





// ALGORITHM A2.3
// Function to compute the nonvanishing basis functions and their derivatives.
function DersBasisFuns(i, p, u, U, n) {
    // Compute nonzero basis functions and their derivatives.
    // Input: i, p, u, U
    // Modified from ALGORITHM A2.2 to store functions and knot differences.
    // Output: ders (derivatives)

    let ndu = Array.from(Array(p + 1), () => new Array(p + 1).fill(0));
    ndu[0][0] = 1.0;
    let left = new Array(p + 1);
    let right = new Array(p + 1);
    let a = Array.from(Array(2), () => new Array(p + 1).fill(0));
    let ders = Array.from(Array(n + 1), () => new Array(p + 1).fill(0));

    for (let j = 1; j <= p; j++) {
        left[j] = u - U[i + 1 - j];
        right[j] = U[i + j] - u;
        let saved = 0.0;

        for (let r = 0; r < j; r++) {
            // Lower triangle
            ndu[j][r] = right[r + 1] + left[j - r];
            let temp = ndu[r][j - 1] / ndu[j][r];

            // Upper triangle
            ndu[r][j] = saved + right[r + 1] * temp;
            saved = left[j - r] * temp;
        }
        ndu[j][j] = saved;
    }

    for (let j = 0; j <= p; j++) {
        // Load the basis functions
        ders[0][j] = ndu[j][p];
    }

    // This section computes the derivatives
    for (let r = 0; r <= p; r++) {
        let s1 = 0;
        let s2 = 1; // alternate rows in array a
        a[0][0] = 1.0;

        // Loop to compute kth derivative
        for (let k = 1; k <= n; k++) {
            let d = 0.0;
            let rk = r - k;
            let pk = p - k;

            if (r >= k) {
                a[s2][0] = a[s1][0] / ndu[pk + 1][rk];
                d = a[s2][0] * ndu[rk][pk];
            }

            let j1 = (rk >= -1) ? 1 : -rk;
            let j2 = (r - 1 <= pk) ? k - 1 : p - r;

            for (let j = j1; j <= j2; j++) {
                a[s2][j] = (a[s1][j] - a[s1][j - 1]) / ndu[pk + 1][rk + j];
                d += a[s2][j] * ndu[rk + j][pk];
            }

            if (r <= pk) {
                a[s2][k] = -a[s1][k - 1] / ndu[pk + 1][r];
                d += a[s2][k] * ndu[r][pk];
            }

            ders[k][r] = d;
            // Switch rows
            let temp = s1;
            s1 = s2;
            s2 = temp;
        }
    }

    // Multiply through by the correct factors (Eq. [2.9])
    let r = p;
    for (let k = 1; k <= n; k++) {
        for (let j = 0; j <= p; j++) {
            ders[k][j] *= r;
        }
        r *= (p - k);
    }

    return ders;
}

// Example usage of ALGORITHM A2.3
// let i = /* the knot span */;
// let p = /* the degree of the B-spline */;
// let u = /* the parameter value */;
// let U = [/* the knot vector */];
// let n = /* the order of the derivative */;
// let ders = DersBasisFuns(i, p, u, U, n);
// console.log(ders); // This will output the derivatives of the basis functions











// ALGORITHM A2.4
// Function to compute the basis function Nip.
function OneBasisFun(p, m, U, i, u) {
    // Compute the basis function Nip
    // Input: p (degree of B-spline), m (upper index of U), U (knot vector), i (knot span), u (parameter value)
    // Output: Nip (the value of the basis function)

    if ((i === 0 && u === U[0]) || (i === m - p - 1 && u === U[m])) {
        // Special cases
        return 1.0;
    }
    if (u < U[i] || u >= U[i + p + 1]) {
        // Local property
        return 0.0;
    }

    let N = new Array(p + 1).fill(0.0);
    // Initialize zeroth-degree functions
    for (let j = 0; j <= p; j++) {
        if (u >= U[i + j] && u < U[i + j + 1]) {
            N[j] = 1.0;
        }
    }

    // Compute triangular table
    for (let k = 1; k <= p; k++) {
        let saved = 0.0;
        if (N[0] === 0.0) {
            saved = 0.0;
        } else {
            saved = ((u - U[i]) * N[0]) / (U[i + k] - U[i]);
        }

        for (let j = 0; j < p - k + 1; j++) {
            let Uleft = U[i + j + 1];
            let Uright = U[i + j + k + 1];

            if (N[j + 1] === 0.0) {
                N[j] = saved;
                saved = 0.0;
            } else {
                let temp = N[j + 1] / (Uright - Uleft);
                N[j] = saved + (Uright - u) * temp;
                saved = (u - Uleft) * temp;
            }
        }
    }

    let Nip = N[0];
    return Nip;
}

// Example usage of ALGORITHM A2.4
// let p = /* the degree of the B-spline */;
// let m = /* the upper index of U */;
// let U = [/* the knot vector */];
// let i = /* the knot span */;
// let u = /* the parameter value */;
// let Nip = OneBasisFun(p, m, U, i, u);
// console.log(Nip); // This will output the value of the basis function








// ALGORITHM A2.5
// Function to compute derivatives of basis function Nip.
function DersOneBasisFun(p, m, U, i, u, n) {
    // Compute derivatives of basis function Nip
    // Input: p (degree of B-spline), m (upper index of U), U (knot vector), i (knot span), u (parameter value), n (derivative order)
    // Output: ders (array of derivatives)

    let ders = new Array(n + 1).fill(0.0);

    // Local property
    if (u < U[i] || u >= U[i + p + 1]) {
        return ders;
    }

    // Initialize zeroth-degree functs
    let N = Array.from(Array(p + 1), () => new Array(p + 1).fill(0));
    N[0][0] = 1.0;
    for (let j = 1; j <= p; j++) {
        if (u >= U[i + j] && u < U[i + j + 1]) {
            N[j][0] = 1.0;
        }
    }

    // Compute full triangular table
    for (let k = 1; k <= p; k++) {
        let saved = 0.0;
        if (N[0][k - 1] === 0.0) {
            saved = 0.0;
        } else {
            saved = ((u - U[i]) * N[0][k - 1]) / (U[i + k] - U[i]);
        }

        for (let j = 0; j < p - k + 1; j++) {
            let Uleft = U[i + j + 1];
            let Uright = U[i + j + k + 1];
            if (N[j + 1][k - 1] === 0.0) {
                N[j][k] = saved;
                saved = 0.0;
            } else {
                let temp = N[j + 1][k - 1] / (Uright - Uleft);
                N[j][k] = saved + (Uright - u) * temp;
                saved = (u - Uleft) * temp;
            }
        }
    }

    // The function value
    ders[0] = N[0][p];

    // Compute the derivatives
    for (let k = 1; k <= n; k++) {
        for (let j = 0; j <= k; j++) {
            N[j][p - k] = N[j][p - k] / (U[i + p - k + j + 1] - U[i + j]);
        }

        let rk = p - k;
        for (let j = 0; j <= rk; j++) {
            let saved = (rk + 1) * N[j][p - k];
            for (let jj = 0; jj < k; jj++) {
                saved = saved - (p - k + jj) * U[i + j + jj] * N[j][p - k - jj - 1];
            }
            ders[k] += saved;
        }
    }

    return ders;
}

// Example usage of ALGORITHM A2.5
// let p = /* the degree of the B-spline */;
// let m = /* the upper index of U */;
// let U = [/* the knot vector */];
// let i = /* the knot span */;
// let u = /* the parameter value */;
// let n = /* the derivative order */;
// let derivatives = DersOneBasisFun(p, m, U, i, u, n);
// console.log(derivatives); // This will output the array of derivatives of the basis function








//--------------------Chapter 3 : B-spline Curves and Surfaces 

// ALGORITHM A3.1
// Function to compute a curve point.
function CurvePoint(n, p, U, P, u) {
    // Compute curve point
    // Input: n (number of control points minus 1), p (degree of the curve), U (knot vector), P (control points), u (parameter value)
    // Output: C (point on the curve)

    let span = FindSpan(n, p, u, U);
    let N = BasisFuns(span, u, p, U);

    let C = [0.0, 0.0, 0.0]; // Assuming a 3-dimensional point for C
    for (let i = 0; i <= p; i++) {
        C[0] += N[i] * P[span - p + i][0]; // x-coordinate
        C[1] += N[i] * P[span - p + i][1]; // y-coordinate
        C[2] += N[i] * P[span - p + i][2]; // z-coordinate (if 3D)
    }

    return C;
}

// Example usage of ALGORITHM A3.1
// let n = /* the number of control points minus 1 */;
// let p = /* the degree of the curve */;
// let U = [/* the knot vector */];
// let P = [/* the array of control points */];
// let u = /* the parameter value */;
// let curvePoint = CurvePoint(n, p, U, P, u);
// console.log(curvePoint); // This will output the computed curve point






// ALGORITHM A3.2
// Function to compute curve derivatives.
function CurveDerivsAlg1(n, p, U, P, u, d) {
    // Compute curve derivatives
    // Input: n (number of control points minus 1), p (degree of the curve), U (knot vector), P (control points), u (parameter value), d (derivative order)
    // Output: CK (derivatives of the curve)

    let du = Math.min(d, p);
    let CK = Array.from({ length: du + 1 }, () => [0.0, 0.0, 0.0]); // Assuming a 3-dimensional space for derivatives

    let span = FindSpan(n, p, u, U);
    let nders = DersBasisFuns(span, u, p, du, U);

    for (let k = 0; k <= du; k++) {
        for (let j = 0; j <= p; j++) {
            if (nders[k][j] !== 0) {
                CK[k][0] += nders[k][j] * P[span - p + j][0]; // x-coordinate derivative
                CK[k][1] += nders[k][j] * P[span - p + j][1]; // y-coordinate derivative
                CK[k][2] += nders[k][j] * P[span - p + j][2]; // z-coordinate derivative (if 3D)
            }
        }
    }

    return CK;
}

// Example usage of ALGORITHM A3.2
// let n = /* the number of control points minus 1 */;
// let p = /* the degree of the curve */;
// let U = [/* the knot vector */];
// let P = [/* the array of control points */];
// let u = /* the parameter value */;
// let d = /* the derivative order */;
// let curveDerivatives = CurveDerivsAlg1(n, p, U, P, u, d);
// console.log(curveDerivatives); // This will output the derivatives of the curve






// ALGORITHM A3.3
// Function to compute control points of curve derivatives.
function CurveDerivCpts(n, p, U, P, d, r1, r2) {
    // Compute control points of curve derivatives
    // Input: n (number of control points minus 1), p (degree of the curve), U (knot vector),
    //        P (control points), d (derivative order), r1, r2 (range of control points)
    // Output: PK (control points of the derivatives)

    let PK = Array.from({ length: d + 1 }, () => []);
    let r = r2 - r1;

    // Initialize control points of the curve derivatives
    for (let i = 0; i <= r; i++) {
        PK[0][i] = P[r1 + i].slice(); // Assuming each control point is an array [x, y, z]
    }

    // Compute the remaining control points
    for (let k = 1; k <= d; k++) {
        let tmp = p - k + 1;
        for (let i = 0; i <= r - k; i++) {
            PK[k][i] = [];
            for (let j = 0; j < P[0].length; j++) { // Iterate over each dimension
                PK[k][i][j] = tmp * (PK[k - 1][i + 1][j] - PK[k - 1][i][j]) / (U[r1 + i + p + 1] - U[r1 + i + k]);
            }
        }
    }

    return PK;
}

// Example usage of ALGORITHM A3.3
// let n = /* the number of control points minus 1 */;
// let p = /* the degree of the curve */;
// let U = [/* the knot vector */];
// let P = [/* the control points as an array of [x, y, z] points */];
// let d = /* the derivative order */;
// let r1 = /* the lower index of the range of control points */;
// let r2 = /* the upper index of the range of control points */;
// let derivativeControlPoints = CurveDerivCpts(n, p, U, P, d, r1, r2);
// console.log(derivativeControlPoints); // This will output the control points for the curve derivatives







// ALGORITHM A3.4
// Function to compute curve derivatives.
function CurveDerivsAlg2(n, p, U, P, u, d) {
    // Compute curve derivatives
    // Input: n (number of control points minus 1), p (degree of the curve), U (knot vector), P (control points), u (parameter value), d (derivative order)
    // Output: CK (curve derivatives at u)

    let du = Math.min(d, p);
    let CK = Array.from({ length: du + 1 }, () => [0.0, 0.0, 0.0]); // Assuming 3D points for CK

    let span = FindSpan(n, p, u, U);
    let N = AllBasisFuns(span, u, p, U); // Assuming AllBasisFuns returns all the non-zero basis functions at u
    let PK = CurveDerivCpts(n, p, U, P, d, span - p, span); // Assuming CurveDerivCpts computes the control points for the derivatives

    for (let k = 0; k <= du; k++) {
        CK[k] = [0.0, 0.0, 0.0]; // Initialize the kth derivative
        for (let j = 0; j <= p - k; j++) {
            CK[k][0] += N[j][p - k] * PK[k][j][0]; // x-coordinate
            CK[k][1] += N[j][p - k] * PK[k][j][1]; // y-coordinate
            CK[k][2] += N[j][p - k] * PK[k][j][2]; // z-coordinate (if 3D)
        }
    }

    return CK;
}

// Example usage of ALGORITHM A3.4
// let n = /* the number of control points minus 1 */;
// let p = /* the degree of the curve */;
// let U = [/* the knot vector */];
// let P = [/* the array of control points as [x, y, z] */];
// let u = /* the parameter value */;
// let d = /* the derivative order */;
// let curveDerivatives = CurveDerivsAlg2(n, p, U, P, u, d);
// console.log(curveDerivatives); // This will output the curve derivatives at u









// ALGORITHM A3.5
// Function to compute surface point.
function SurfacePoint(n, p, U, m, q, V, P, u, v) {
    // Compute surface point
    // Input: n, p, U (knot vector in u direction), m, q, V (knot vector in v direction), P (control point grid), u, v (parameter values)
    // Output: S (point on the surface)

    let uspan = FindSpan(n, p, u, U);
    let Nu = BasisFuns(uspan, u, p, U);

    let vspan = FindSpan(m, q, v, V);
    let Nv = BasisFuns(vspan, v, q, V);

    let uind = uspan - p;
    let S = [0.0, 0.0, 0.0]; // Assuming a 3-dimensional point for S

    for (let l = 0; l <= q; l++) {
        let temp = [0.0, 0.0, 0.0]; // Temporary point to accumulate the influence of the basis functions in u direction
        let vind = vspan - q + l;
        for (let k = 0; k <= p; k++) {
            let uindk = uind + k;
            temp[0] += Nu[k] * P[uindk][vind][0]; // x-coordinate
            temp[1] += Nu[k] * P[uindk][vind][1]; // y-coordinate
            temp[2] += Nu[k] * P[uindk][vind][2]; // z-coordinate (if 3D)
        }
        S[0] += Nv[l] * temp[0];
        S[1] += Nv[l] * temp[1];
        S[2] += Nv[l] * temp[2];
    }

    return S;
}

// Example usage of ALGORITHM A3.5
// let n = /* number of control points in u direction minus 1 */;
// let p = /* degree of the surface in u direction */;
// let U = [/* knot vector in u direction */];
// let m = /* number of control points in v direction minus 1 */;
// let q = /* degree of the surface in v direction */;
// let V = [/* knot vector in v direction */];
// let P = [/* control point grid as an array of arrays of [x, y, z] points */];
// let u = /* parameter value in u direction */;
// let v = /* parameter value in v direction */;
// let surfacePoint = SurfacePoint(n, p, U, m, q, V, P, u, v);
// console.log(surfacePoint); // This will output the surface point at (u, v)






// ALGORITHM A3.6
// Function to compute surface derivatives.
function SurfaceDerivsAlg1(n, p, U, m, q, V, P, u, v, d) {
    // Compute surface derivatives
    // Input: n (number of control points in u direction minus 1), p (degree in u direction), U (knot vector in u direction),
    //        m (number of control points in v direction minus 1), q (degree in v direction), V (knot vector in v direction),
    //        P (control point grid), u, v (parameter values), d (order of derivatives)
    // Output: SKL (surface derivatives)

    let du = Math.min(d, p);
    let dv = Math.min(d, q);
    let SKL = Array.from(Array(du + 1), () => Array(dv + 1).fill(null).map(() => [0.0, 0.0, 0.0])); // Assuming 3D points for SKL

    let uspan = FindSpan(n, p, u, U);
    let Nu = DersBasisFuns(uspan, u, p, du, U); // Assuming DersBasisFuns returns the derivatives of the basis functions

    let vspan = FindSpan(m, q, v, V);
    let Nv = DersBasisFuns(vspan, v, q, dv, V); // Assuming DersBasisFuns returns the derivatives of the basis functions

    for (let k = 0; k <= du; k++) {
        for (let s = 0; s <= dv; s++) {
            let temp = [0.0, 0.0, 0.0]; // Temporary point to accumulate the influence of the basis functions
            for (let r = 0; r <= p; r++) {
                for (let t = 0; t <= q; t++) {
                    let point = P[uspan - p + r][vspan - q + t];
                    let weight = Nu[k][r] * Nv[s][t];
                    temp[0] += point[0] * weight;
                    temp[1] += point[1] * weight;
                    temp[2] += point[2] * weight; // Assuming P is a 3D control point
                }
            }
            SKL[k][s] = temp;
        }
    }

    return SKL;
}

// Example usage of ALGORITHM A3.6
// let n = /* number of control points in u direction minus 1 */;
// let p = /* degree of the surface in u direction */;
// let U = [/* knot vector in u direction */];
// let m = /* number of control points in v direction minus 1 */;
// let q = /* degree of the surface in v direction */;
// let V = [/* knot vector in v direction */];
// let P = [/* control point grid as an array of arrays of [x, y, z] points */];
// let u = /* parameter value in u direction */;
// let v = /* parameter value in v direction */;
// let d = /* order of derivatives */;
// let surfaceDerivatives = SurfaceDerivsAlg1(n, p, U, m, q, V, P, u, v, d);
// console.log(surfaceDerivatives); // This will output the surface derivatives







// ALGORITHM A3.7
// Function to compute control points of derivative surfaces.
function SurfaceDerivCpts(n, p, U, m, q, V, P, d, r1, r2, s1, s2) {
    // Compute control points of derivative surfaces
    // Input: n, p, U (knot vector in u), m, q, V (knot vector in v), P (control points), 
    //        d (derivative order), r1, r2, s1, s2 (control point range)
    // Output: PKL (control points for the derivative surfaces)

    let du = Math.min(d, p);
    let dv = Math.min(d, q);
    let PKL = Array.from(Array(du + 1), () => Array.from(Array(dv + 1), () => []));
    let r = r2 - r1;
    let s = s2 - s1;
    let temp = [];

    // Compute control points for the u-direction derivatives
    for (let j = s1; j <= s2; j++) {
        // Each P[][] is a row for CurveDerivCpts
        let row = Array.from({ length: n + 1 }, (_, i) => P[i][j]);
        temp = CurveDerivCpts(n, p, U, row, du, r1, r2); // Compute curve derivative control points in u
        for (let k = 0; k <= du; k++) {
            for (let i = 0; i <= r - k; i++) {
                PKL[k][0][i + j - s1] = temp[k][i]; // Assign computed control points
            }
        }
    }

    // Compute control points for the v-direction derivatives
    for (let k = 0; k <= du; k++) {
        for (let i = 0; i <= r - k; i++) {
            // Each PKL[k][0][] is a row for CurveDerivCpts
            let col = PKL[k][0].slice(i, s + 1);
            temp = CurveDerivCpts(m, q, V, col, dv, s1, s2); // Compute curve derivative control points in v
            for (let l = 1; l <= dv; l++) {
                for (let j = 0; j <= s - l; j++) {
                    PKL[k][l][i][j] = temp[l][j]; // Assign computed control points
                }
            }
        }
    }

    return PKL;
}

// Example usage of ALGORITHM A3.7
// let n = /* the number of control points in u direction minus 1 */;
// let p = /* the degree in u direction */;
// let U = [/* the knot vector in u direction */];
// let m = /* the number of control points in v direction minus 1 */;
// let q = /* the degree in v direction */;
// let V = [/* the knot vector in v direction */];
// let P = [/* the control point grid */];
// let d = /* the derivative order */;
// let r1 = /* the start index in u direction */;
// let r2 = /* the end index in u direction */;
// let s1 = /* the start index in v direction */;
// let s2 = /* the end index in v direction */;
// let derivativeControlPoints = SurfaceDerivCpts(n, p, U, m, q, V, P, d, r1, r2, s1, s2);
// console.log(derivativeControlPoints); // This will output the control points for the surface derivatives







// ALGORITHM A3.8
// Function to compute surface derivatives.
function SurfaceDerivsAlg2(n, p, U, m, q, V, P, u, v, d) {
    // Compute surface derivatives
    // Input: n, p, U (knot vector in u), m, q, V (knot vector in v), P (control points), u, v (parameter values), d (order of derivatives)
    // Output: SKL (surface derivatives at (u, v))

    let du = Math.min(d, p);
    let dv = Math.min(d, q);
    let SKL = Array.from(Array(du + 1), () => Array.from(Array(dv + 1), () => [0.0, 0.0, 0.0])); // Assuming 3D points for SKL

    let uspan = FindSpan(n, p, u, U);
    let Nu = AllBasisFuns(uspan, u, p, U); // Assuming AllBasisFuns returns all non-zero basis functions at u

    let vspan = FindSpan(m, q, v, V);
    let Nv = AllBasisFuns(vspan, v, q, V); // Assuming AllBasisFuns returns all non-zero basis functions at v

    let PKL = SurfaceDerivCpts(n, p, U, m, q, V, P, d, uspan - p, uspan, vspan - q, vspan); // Assuming SurfaceDerivCpts computes the control points for the surface derivatives

    for (let k = 0; k <= du; k++) {
        for (let l = 0; l <= dv; l++) {
            SKL[k][l] = [0.0, 0.0, 0.0]; // Initialize the derivative
            for (let i = 0; i <= q - l; i++) {
                let temp = [0.0, 0.0, 0.0]; // Temporary point to accumulate the influence of the basis functions
                for (let j = 0; j <= p - k; j++) {
                    temp[0] += Nu[j][p - k] * PKL[k][l][j][i][0]; // x-coordinate
                    temp[1] += Nu[j][p - k] * PKL[k][l][j][i][1]; // y-coordinate
                    temp[2] += Nu[j][p - k] * PKL[k][l][j][i][2]; // z-coordinate (if 3D)
                }
                SKL[k][l][0] += Nv[i][q - l] * temp[0];
                SKL[k][l][1] += Nv[i][q - l] * temp[1];
                SKL[k][l][2] += Nv[i][q - l] * temp[2];
            }
        }
    }

    return SKL;
}

// Example usage of ALGORITHM A3.8
// let n = /* the number of control points in u direction minus 1 */;
// let p = /* the degree in u direction */;
// let U = [/* the knot vector in u direction */];
// let m = /* the number of control points in v direction minus 1 */;
// let q = /* the degree in v direction */;
// let V = [/* the knot vector in v direction */];
// let P = [/* the control point grid */];
// let u = /* parameter value in u direction */;
// let v = /* parameter value in v direction */;
// let d = /* the order of derivatives */;
// let surfaceDerivatives = SurfaceDerivsAlg2(n, p, U, m, q, V, P, u, v, d);
// console.log(surfaceDerivatives); // This will output the surface derivatives at (u, v)





//--------------------Chapter 4 : Rational B-spline Curves and Surfaces 




// ALGORITHM A4.1
// Function to compute point on rational B-spline curve.
function CurvePoint(n, p, U, Pw, u) {
    // Compute point on rational B-spline curve
    // Input: n (number of control points minus 1), p (degree of the curve), U (knot vector), Pw (control points with weights), u (parameter value)
    // Output: C (point on the curve)

    let span = FindSpan(n, p, u, U);
    let N = BasisFuns(span, u, p, U);
    let Cw = [0.0, 0.0, 0.0, 0.0]; // Assuming 3D homogeneous points for Cw

    for (let j = 0; j <= p; j++) {
        Cw[0] += N[j] * Pw[span - p + j][0]; // x-coordinate
        Cw[1] += N[j] * Pw[span - p + j][1]; // y-coordinate
        Cw[2] += N[j] * Pw[span - p + j][2]; // z-coordinate
        Cw[3] += N[j] * Pw[span - p + j][3]; // weight
    }

    let C = [Cw[0] / Cw[3], Cw[1] / Cw[3], Cw[2] / Cw[3]]; // Divide by weight to get the Cartesian coordinates
    return C;
}

// Example usage of ALGORITHM A4.1
// let n = /* the number of control points minus 1 */;
// let p = /* the degree of the curve */;
// let U = [/* the knot vector */];
// let Pw = [/* the control points with weights as an array of [x, y, z, w] */];
// let u = /* the parameter value */;
// let curvePoint = CurvePoint(n, p, U, Pw, u);
// console.log(curvePoint); // This will output the computed point on the curve





// ALGORITHM A4.2
// Function to compute C(u) derivatives from Cw(u) derivatives.
function RatCurveDerivs(Aders, wders, d) {
    // Compute C(u) derivatives from Cw(u) derivatives
    // Input: Aders (derivatives of the weighted points), wders (derivatives of the weights), d (derivative order)
    // Output: CK (derivatives of the curve points in Cartesian coordinates)

    let CK = new Array(d + 1).fill(null).map(() => [0.0, 0.0, 0.0]); // Assuming 3D points for CK

    for (let k = 0; k <= d; k++) {
        let v = [...Aders[k]]; // Copy the k-th derivative of A
        for (let i = 1; i <= k; i++) {
            // Binomial coefficient 'Bin' is assumed to be defined elsewhere and returns the binomial coefficient (n choose k)
            let bin = Bin(k, i);
            v[0] -= bin * wders[i] * CK[k - i][0]; // x-coordinate
            v[1] -= bin * wders[i] * CK[k - i][1]; // y-coordinate
            v[2] -= bin * wders[i] * CK[k - i][2]; // z-coordinate
        }
        CK[k][0] = v[0] / wders[0];
        CK[k][1] = v[1] / wders[0];
        CK[k][2] = v[2] / wders[0];
    }

    return CK;
}

// Helper function: Binomial coefficient
function Bin(n, k) {
    let coeff = 1;
    for (let x = n - k + 1; x <= n; x++) coeff *= x;
    for (let x = 1; x <= k; x++) coeff /= x;
    return coeff;
}

// Example usage of ALGORITHM A4.2
// let Aders = [/* array of derivatives of the weighted points */];
// let wders = [/* array of derivatives of the weights */];
// let d = /* the derivative order */;
// let curveDerivatives = RatCurveDerivs(Aders, wders, d);
// console.log(curveDerivatives); // This will output the derivatives of the curve points in Cartesian coordinates







// ALGORITHM A4.3
// Function to compute point on rational B-spline surface.
function SurfacePoint(n, p, U, m, q, V, Pw, u, v) {
    // Compute point on rational B-spline surface
    // Input: n (number of control points in u minus 1), p (degree in u), U (knot vector in u),
    //        m (number of control points in v minus 1), q (degree in v), V (knot vector in v),
    //        Pw (control points with weights), u, v (parameter values)
    // Output: S (point on the surface)

    let uspan = FindSpan(n, p, u, U);
    let Nu = BasisFuns(uspan, u, p, U);

    let vspan = FindSpan(m, q, v, V);
    let Nv = BasisFuns(vspan, v, q, V);

    let S = [0.0, 0.0, 0.0, 0.0]; // Assuming a 3D point with weight for S
    for (let l = 0; l <= q; l++) {
        let temp = [0.0, 0.0, 0.0, 0.0]; // Temporary point to accumulate the influence of the basis functions in u
        for (let k = 0; k <= p; k++) {
            let point = Pw[uspan - p + k][vspan - q + l];
            for (let i = 0; i < point.length; i++) {
                temp[i] += Nu[k] * point[i]; // Multiply point by basis function value
            }
        }
        for (let i = 0; i < temp.length; i++) {
            S[i] += Nv[l] * temp[i]; // Sum up the control point contributions in v
        }
    }

    // Divide by the weight to obtain the Cartesian coordinates
    let Sw = S[S.length - 1];
    for (let i = 0; i < S.length - 1; i++) {
        S[i] /= Sw;
    }

    return S.slice(0, -1); // Exclude the weight from the final output
}

// Example usage of ALGORITHM A4.3
// let n = /* the number of control points in u direction minus 1 */;
// let p = /* the degree of the surface in u direction */;
// let U = [/* the knot vector in u direction */];
// let m = /* the number of control points in v direction minus 1 */;
// let q = /* the degree of the surface in v direction */;
// let V = [/* the knot vector in v direction */];
// let Pw = [/* the weighted control points as an array of [x, y, z, w] */];
// let u = /* the parameter value in u direction */;
// let v = /* the parameter value in v direction */;
// let surfacePoint = SurfacePoint(n, p, U, m, q, V, Pw, u, v);
// console.log(surfacePoint); // This will output the computed point on the surface








// ALGORITHM A4.4
// Function to compute S(u,v) derivatives from Sw(u,v) derivatives.
function RatSurfaceDerivs(Aders, wders, d) {
    // Compute S(u,v) derivatives from Sw(u,v) derivatives
    // Input: Aders (derivatives of the weighted points), wders (derivatives of the weights), d (derivative order)
    // Output: SKL (derivatives of the surface points in Cartesian coordinates)

    let SKL = Array.from(Array(d + 1), () => Array(d + 1).fill(null).map(() => [0.0, 0.0, 0.0])); // Assuming 3D points for SKL

    for (let k = 0; k <= d; k++) {
        for (let l = 0; l <= d - k; l++) {
            let v = [...Aders[k][l]]; // Copy the derivative vector

            // Subtract binomial-weighted lower order derivatives
            for (let j = 1; j <= l; j++) {
                v = v.map((val, idx) => val - Bin(l, j) * wders[0][j] * SKL[k][l - j][idx]);
            }
            for (let i = 1; i <= k; i++) {
                v = v.map((val, idx) => val - Bin(k, i) * wders[i][0] * SKL[k - i][l][idx]);
                let v2 = [0.0, 0.0, 0.0];
                for (let j = 1; j <= l; j++) {
                    v2 = v2.map((val, idx) => val + Bin(l, j) * wders[i][j] * SKL[k - i][l - j][idx]);
                }
                v = v.map((val, idx) => val - Bin(k, i) * v2[idx]);
            }
            // Divide by the weight to get the Cartesian coordinates
            SKL[k][l] = v.map(val => val / wders[0][0]);
        }
    }

    return SKL;
}

// Example usage of ALGORITHM A4.4
// let Aders = [/* array of derivatives of the weighted points */];
// let wders = [/* array of derivatives of the weights */];
// let d = /* the derivative order */;
// let surfaceDerivatives = RatSurfaceDerivs(Aders, wders, d);
// console.log(surfaceDerivatives); // This will output the derivatives of the surface points in Cartesian coordinates







//--------------------Chapter 5 : Fundamental Geometric Algorithms 







// ALGORITHM A5.1
// Function to perform knot insertion on a NURBS curve.
function CurveKnotIns(n, p, UP, Pw, u, k, s, r) {
    // Compute new curve from knot insertion
    // Input: n (number of control points minus 1), p (degree of curve), UP (original knot vector),
    //        Pw (original control points), u (knot to insert), k (knot span), s (multiplicity of knot u),
    //        r (number of times to insert knot u)
    // Output: nq (new number of control points minus 1), UQ (new knot vector), Qw (new control points)

    let mp = n + p + 1;
    let nq = n + r;
    let UQ = new Array(mp + r + 1);
    let Qw = new Array(n + 1 + r);
    let Rw = new Array(p + 1);

    // Load new knot vector
    for (let i = 0; i <= k; i++) UQ[i] = UP[i];
    for (let i = 1; i <= r; i++) UQ[k + i] = u;
    for (let i = k + 1; i <= mp; i++) UQ[i + r] = UP[i];

    // Save unaltered control points
    for (let i = 0; i <= k - p; i++) Qw[i] = Pw[i];
    for (let i = k - s; i <= n; i++) Qw[i + r] = Pw[i];
    for (let i = 0; i <= p - s; i++) Rw[i] = Pw[k - p + i];

    // Insert the knot r times
    for (let j = 1; j <= r; j++) {
        let L = k - p + j;
        for (let i = 0; i <= p - j - s; i++) {
            let alpha = (u - UP[L + i]) / (UP[i + k + 1] - UP[L + i]);
            Rw[i] = {
                x: alpha * Rw[i + 1].x + (1.0 - alpha) * Rw[i].x,
                y: alpha * Rw[i + 1].y + (1.0 - alpha) * Rw[i].y,
                z: alpha * Rw[i + 1].z + (1.0 - alpha) * Rw[i].z,
                w: alpha * Rw[i + 1].w + (1.0 - alpha) * Rw[i].w
            };
        }
        Qw[L] = Rw[0];
        Qw[k + r - j - s] = Rw[p - j - s];
    }

    // Load remaining control points
    for (let i = L + 1; i < k - s; i++) Qw[i] = Rw[i - L];

    return { nq, UQ, Qw };
}

// Example usage of ALGORITHM A5.1
// let n = /* number of control points minus 1 */;
// let p = /* degree of curve */;
// let UP = [/* original knot vector */];
// let Pw = [/* original weighted control points as an array of {x, y, z, w} */];
// let u = /* knot to insert */;
// let k = /* knot span */;
// let s = /* multiplicity of knot u */;
// let r = /* number of times to insert knot u */;
// let { nq, UQ, Qw } = CurveKnotIns(n, p, UP, Pw, u, k, s, r);
// console.log(UQ); // New knot vector
// console.log(Qw); // New control points








// ALGORITHM A5.2
// Function to compute a point on a rational B-spline curve.
function curvePntByCornerCut(np, UP, w, u) {
    // Compute point on rational B-spline curve
    // Input: np (control points), UP (knot vector), w (weight), u (parameter value)
    // Output: C (computed point on the curve)

    let n = np.length - 1;
    let p = UP.length - n - 1;
    let C, k, s, r, alpha;
    let Rw = new Array(p);

    // Endpoints are special cases
    if (u === UP[0]) {
        C = divideVectorByScalar(np[0], w);
        return C;
    }
    if (u === UP[n + p + 1]) {
        C = divideVectorByScalar(np[n], w);
        return C;
    }

    // General case
    [k, s] = findSpanMult(n, p, u, UP);
    r = p - s;
    for (let i = 0; i <= r; i++) {
        Rw[i] = np[k - p + i];
    }
    for (let j = 1; j <= r; j++) {
        for (let i = 0; i <= r - j; i++) {
            alpha = (u - UP[k - p + j + i]) / (UP[i + k + 1] - UP[k - p + j + i]);
            Rw[i] = {
                x: alpha * Rw[i + 1].x + (1.0 - alpha) * Rw[i].x,
                y: alpha * Rw[i + 1].y + (1.0 - alpha) * Rw[i].y,
                z: alpha * Rw[i + 1].z + (1.0 - alpha) * Rw[i].z,
                w: alpha * Rw[i + 1].w + (1.0 - alpha) * Rw[i].w
            };
        }
    }
    C = divideVectorByScalar(Rw[0], w);
    return C;
}

// Helper functions
function divideVectorByScalar(vector, scalar) {
    return {
        x: vector.x / scalar,
        y: vector.y / scalar,
        z: vector.z / scalar,
        w: vector.w / scalar
    };
}

// Example usage of ALGORITHM A5.2
// let np = [/* control points as an array of {x, y, z, w} */];
// let UP = [/* knot vector */];
// let w = /* weight */;
// let u = /* parameter value */;
// let C = curvePntByCornerCut(np, UP, w, u);
// console.log(C); // Computed point on the curve








// ALGORITHM A5.3
// SurfaceKnotIns: Algorithm for surface knot insertion in NURBS.
// This function inserts a knot into a NURBS surface in either the U or V direction.
function SurfaceKnotIns(np, p, UP, mp, q, VP, Pw, dir, uv, k, s, r, nq, UQ, mq, VQ, Qw) {
    const U_DIRECTION = 0; // Assuming constant for U direction
    const V_DIRECTION = 1; // Assuming constant for V direction
    let alpha = []; // Initialize alpha array as needed

    if (dir === U_DIRECTION) {
        // U-direction algorithm implementation
        // Save the alphas
        for (let j = 1; j <= r; j++) {
            let L = k - p + j;
            for (let i = 0; i <= p - j - s; i++) {
                alpha[i][j] = (uv - UP[L + i]) / (UP[i + k + 1] - UP[L + i]);
            }
        }
        // For each row do
        for (let row = 0; row <= mp; row++) {
            // Save unaltered control points
            for (let i = 0; i <= k - p; i++) Qw[i][row] = Pw[i][row];
            for (let i = k - s; i <= np; i++) Qw[i + r][row] = Pw[i][row];
            // Load auxiliary control points
            for (let i = 0; i <= p - s; i++) Rw[i] = Pw[k - p + i][row];
            // Insert the knot r times
            for (let j = 1; j <= r; j++) {
                let L = k - p + j;
                for (let i = 0; i <= p - j - s; i++) {
                    Rw[i] = alpha[i][j] * Rw[i + 1] + (1.0 - alpha[i][j]) * Rw[i];
                }
                Qw[L][row] = Rw[0];
                Qw[k + r - j - s][row] = Rw[p - j - s];
            }
            // Load the remaining control points
            for (let i = L + 1; i < k - s; i++) Qw[i][row] = Rw[i - L];
        }
    } else if (dir === V_DIRECTION) {
        // V-direction algorithm implementation
        // Save the alphas
        for (let j = 1; j <= r; j++) {
            let L = k - q + j;
            for (let i = 0; i <= q - j - s; i++) {
                alpha[i][j] = (uv - VP[L + i]) / (VP[i + k + 1] - VP[L + i]);
            }
        }
        // For each column do
        for (let col = 0; col <= np; col++) {
            // Save unaltered control points
            for (let i = 0; i <= k - q; i++) Qw[col][i] = Pw[col][i];
            for (let i = k - s; i <= mp; i++) Qw[col][i + r] = Pw[col][i];
            // Load auxiliary control points
            for (let i = 0; i <= q - s; i++) Rw[i] = Pw[col][k - q + i];
            // Insert the knot r times
            for (let j = 1; j <= r; j++) {
                let L = k - q + j;
                for (let i = 0; i <= q - j - s; i++) {
                    Rw[i] = alpha[i][j] * Rw[i + 1] + (1.0 - alpha[i][j]) * Rw[i];
                }
                Qw[col][L] = Rw[0];
                Qw[col][k + r - j - s] = Rw[q - j - s];
            }
            // Load the remaining control points
            for (let i = L + 1; i < k - s; i++) Qw[col][i] = Rw[i - L];
        }
    }

    // Return the updated control points and knot vectors
    return { Qw: Qw, UQ: UQ, VQ: VQ, nq: nq, mq: mq };

}


// Example usage of ALGORITHM A5.3
// let np = /* number of control points in U minus one */;
// let p = /* degree in U direction */;
// let UP = /* knot vector in U */;
// let mp = /* number of control points in V minus one */;
// let q = /* degree in V direction */;
// let VP = /* knot vector in V */;
// let Pw = /* control points array */;
// let dir = /* direction for knot insertion (0 for U, 1 for V) */;
// let uv = /* knot value to insert */;
// let k = /* span where knot is to be inserted */;
// let s = /* multiplicity of knot */;
// let r = /* number of times knot is to be inserted */;
// let nq = /* new number of control points in U (or V) minus one */;
// let UQ = /* new knot vector in U (or V) */;
// let mq = /* new number of control points in V (or U) minus one */;
// let VQ = /* new knot vector in V (or U) */;
// let Qw = /* new control points array after insertion */;
// SurfaceKnotIns(np, p, UP, mp, q, VP, Pw, dir, uv, k, s, r, nq, UQ, mq, VQ, Qw);
// console.log('New Knot Vector:', UQ or VQ);
// console.log('New Control Points:', Qw);








// ALGORITHM A5.4
// RefineKnotVectCurve: Algorithm for knot refinement in NURBS curve.
// This algorithm refines a curve by inserting a given set of knots.
function RefineKnotVectCurve(n, p, U, Pw, X, r, Ubar, Qw) {
    let m = n + p + 1;
    let a = FindSpan(n, p, X[0], U);  // Assuming FindSpan is implemented
    let b = FindSpan(n, p, X[r], U);  // Assuming FindSpan is implemented
    b++;

    for (let j = 0; j <= a - p; j++) Qw[j] = Pw[j];
    for (let j = b - 1; j <= n; j++) Qw[j + r + 1] = Pw[j];
    for (let j = 0; j <= a; j++) Ubar[j] = U[j];
    for (let j = b + p; j <= m; j++) Ubar[j + r + 1] = U[j];

    let i = b + p - 1, k = b + p + r;
    for (let j = r; j >= 0; j--) {
        while (X[j] <= U[i] && i > a) {
            Qw[k - p - 1] = Pw[i - p - 1];
            Ubar[k] = U[i];
            k--; i--;
        }
        Qw[k - p - 1] = Qw[k - p];
        for (let l = 1; l <= p; l++) {
            let ind = k - p + l;
            let alfa = Ubar[k + l] - X[j];
            if (Math.abs(alfa) === 0.0) {
                Qw[ind - 1] = Qw[ind];
            } else {
                alfa = alfa / (Ubar[k + l] - U[i - p + l]);
                Qw[ind - 1] = alfa * Qw[ind - 1] + (1.0 - alfa) * Qw[ind];
            }
        }
        Ubar[k] = X[j];
        k--;
    }
}


// Example usage of ALGORITHM A5.4
// let n = /* number of control points minus one */;
// let p = /* degree of the curve */;
// let U = /* original knot vector */;
// let Pw = /* control points */;
// let X = /* new knots to insert */;
// let r = X.length - 1;
// let Ubar = new Array(U.length + r + 1); // New knot vector
// let Qw = new Array(Pw.length + r + 1); // New control points
// RefineKnotVectCurve(n, p, U, Pw, X, r, Ubar, Qw);
// console.log('New Knot Vector:', Ubar);
// console.log('New Control Points:', Qw);






// ALGORITHM A5.5
// RefineKnotVectCurve: Algorithm for refining the knot vector of a NURBS curve.
// This function refines a curve by inserting a set of new knots (X) into the original knot vector (U).
function RefineKnotVectCurve(n, p, U, Pw, X, r) {
    let m = n + p + 1;
    let Ubar = new Array(m + r + 1);
    let Qw = new Array(n + r + 1);

    for (let i = 0; i <= p; i++) {
        Ubar[i] = U[i];
        Ubar[m + r + i + 1] = U[m + i];
    }

    for (let i = 0; i <= n; i++) {
        Qw[i] = Pw[i];
    }

    let i = p;
    let k = p;
    let j = 0;

    while (j <= r) {
        while (i <= m && X[j] >= U[i]) {
            Ubar[k + 1] = U[i];
            Qw[k] = Pw[i - p];
            k++;
            i++;
        }

        Ubar[k + 1] = X[j];
        j++;

        for (let l = 1; l <= p; l++) {
            Qw[k - l] = Qw[k - l + 1];
        }
    }

    return { Ubar, Qw };
}

// Example usage of ALGORITHM A5.5
// let n = 3; // Example value for number of control points minus one
// let p = 2; // Example value for degree of the curve
// let U = [0, 0, 0, 1, 1, 1]; // Example original knot vector
// let Pw = [/* Control points array */];
// let X = [0.5, 0.75]; // Example array of new knots to be inserted
// let r = X.length - 1;
// let result = RefineKnotVectCurve(n, p, U, Pw, X, r);
// console.log('New Knot Vector:', result.Ubar);
// console.log('New Control Points:', result.Qw);





// ALGORITHM A5.6
// DecomposeCurve: Algorithm for decomposing a NURBS curve into Bézier segments.
// This function decomposes a given NURBS curve into its constituent Bézier segments.
function DecomposeCurve(n, p, U, Pw) {
    let m = n + p + 1;
    let a = p;
    let b = p + 1;
    let nb = 0;
    let Qw = [];
    Qw[nb] = [];

    for (let i = 0; i <= p; i++) {
        Qw[nb][i] = Pw[i];
    }

    while (b < m) {
        let i = b;
        while (b < m && U[b + 1] === U[b]) {
            b++;
        }
        let mult = b - i + 1;
        if (mult < p) {
            let numer = U[b] - U[a];
            let alphas = [];
            for (let j = p; j > mult; j--) {
                alphas[j - mult - 1] = numer / (U[a + j] - U[a]);
            }
            let r = p - mult;
            for (let j = 1; j <= r; j++) {
                let save = r - j;
                let s = mult + j;
                for (let k = p; k >= s; k--) {
                    let alpha = alphas[k - s];
                    Qw[nb][k] = alpha * Qw[nb][k] + (1.0 - alpha) * Qw[nb][k - 1];
                }
                if (b < m) {
                    Qw[nb + 1][save] = Qw[nb][p];
                }
            }
        }
        nb++;
        if (b < m) {
            Qw[nb] = [];
            for (let i = p - mult; i <= p; i++) {
                Qw[nb][i] = Pw[b - p + i];
            }
            a = b;
            b++;
        }
    }

    return Qw;
}

// Example usage of ALGORITHM A5.6
// let n = /* number of control points minus one */;
// let p = /* degree of the curve */;
// let U = /* knot vector */;
// let Pw = /* control points array */;
// let bezierSegments = DecomposeCurve(n, p, U, Pw);
// console.log('Bézier Segments:', bezierSegments);









// ALGORITHM A5.7
// DecomposeSurface: Algorithm for decomposing a NURBS surface into Bézier patches.
// This function decomposes a given NURBS surface into its constituent Bézier patches in either the U or V direction.
function DecomposeSurface(n, p, U, m, q, V, Pw, dir) {
    const U_DIRECTION = 0; // Assuming constant for U direction
    const V_DIRECTION = 1; // Assuming constant for V direction
    let nb = 0;
    let Qw = [];

    if (dir === U_DIRECTION) {
        let a = p, b = p + 1;
        Qw[nb] = [];

        for (let i = 0; i <= p; i++) {
            Qw[nb][i] = [];
            for (let row = 0; row <= m; row++) {
                Qw[nb][i][row] = Pw[i][row];
            }
        }

        while (b < m) {
            let i = b;
            while (b < m && U[b + 1] === U[b]) {
                b++;
            }
            let mult = b - i + 1;
            if (mult < p) {
                for (let j = p; j > mult; j--) {
                    for (let k = p; k >= j; k--) {
                        let alpha = (U[b] - U[a + k]) / (U[a + j] - U[a + k]);
                        for (let col = 0; col <= n; col++) {
                            Qw[nb][k][col] = alpha * Qw[nb][k][col] + (1.0 - alpha) * Qw[nb][k - 1][col];
                        }
                    }
                }
            }

            nb++;
            if (b < m) {
                Qw[nb] = [];
                for (let i = p - mult; i <= p; i++) {
                    Qw[nb][i] = [];
                    for (let row = 0; row <= m; row++) {
                        Qw[nb][i][row] = Pw[b - p + i][row];
                    }
                }
                a = b;
                b++;
            }
        }
    }
    else if (dir === V_DIRECTION) {
        let a = q, b = q + 1;
        Qw[nb] = [];

        for (let col = 0; col <= n; col++) {
            Qw[nb][col] = [];
            for (let j = 0; j <= q; j++) {
                Qw[nb][col][j] = Pw[col][j];
            }
        }

        while (b < m) {
            let i = b;
            while (b < m && V[b + 1] === V[b]) {
                b++;
            }
            let mult = b - i + 1;
            if (mult < q) {
                for (let j = q; j > mult; j--) {
                    for (let k = q; k >= j; k--) {
                        let alpha = (V[b] - V[a + k]) / (V[a + j] - V[a + k]);
                        for (let row = 0; row <= n; row++) {
                            Qw[nb][row][k] = alpha * Qw[nb][row][k] + (1.0 - alpha) * Qw[nb][row][k - 1];
                        }
                    }
                }
            }

            nb++;
            if (b < m) {
                Qw[nb] = [];
                for (let col = 0; col <= n; col++) {
                    Qw[nb][col] = [];
                    for (let j = q - mult; j <= q; j++) {
                        Qw[nb][col][j] = Pw[col][b - q + j];
                    }
                }
                a = b;
                b++;
            }
        }
    }

    return Qw;
}

// Example usage of ALGORITHM A5.7
// let n = /* number of control points in U minus one */;
// let p = /* degree in U direction */;
// let U = /* knot vector in U */;
// let m = /* number of control points in V minus one */;
// let q = /* degree in V direction */;
// let V = /* knot vector in V */;
// let Pw = /* control points array */;
// let dir = /* direction for decomposition (0 for U, 1 for V) */;
// let bezierPatches = DecomposeSurface(n, p, U, m, q, V, Pw, dir);
// console.log('Bézier Patches:', bezierPatches);






// ALGORITHM A5.8
// RemoveCurveKnot: Algorithm for removing a knot from a NURBS curve.
// This function attempts to remove a knot 'u' from a NURBS curve 'num' times.
// Input: n (number of control points minus 1), p (curve degree), U (knot vector),
//        Pw (control points), u (knot to be removed), r (knot span index),
//        s (multiplicity of the knot), num (number of times to remove the knot)
// Output: The function updates the control points and the knot vector in place.
function RemoveCurveKnot(n, p, U, Pw, u, r, s, num) {
    let m = n + p + 1;
    let ord = p + 1;
    let fout = (2 * r - s - p) / 2;
    let last = r - s;
    let first = r - p;
    let temp = [];
    let t;

    for (t = 0; t < num; t++) {
        let off = first - 1;
        temp[0] = Pw[off];
        temp[last + 1 - off] = Pw[last + 1];

        let i = first, j = last;
        let ii = 1, jj = last - off;
        let remflag = 0;

        while (j - i > t) {
            let alfi = (u - U[i]) / (U[i + ord + t] - U[i]);
            let alfj = (u - U[j - t]) / (U[j + ord] - U[j - t]);
            temp[ii] = (Pw[i] - (1.0 - alfi) * temp[ii - 1]) / alfi;
            temp[jj] = (Pw[j] - alfj * temp[jj + 1]) / (1.0 - alfj);
            i++; ii++;
            j--; jj--;
        }

        if (j - i < t) {
            if (Distance4D(temp[ii - 1], temp[jj + 1]) <= TOL) {
                remflag = 1;
            }
        } else {
            let alfi = (u - U[i]) / (U[i + ord + t] - U[i]);
            if (Distance4D(Pw[i], alfi * temp[ii + t + 1] + (1.0 - alfi) * temp[ii - 1]) <= TOL) {
                remflag = 1;
            }
        }

        if (remflag === 0) {
            break;
        } else {
            i = first; j = last;
            while (j - i > t) {
                Pw[i] = temp[i - off];
                Pw[j] = temp[j - off];
                i++; j--;
            }
        }

        first--; last++;
    }

    if (t === 0) {
        return;
    }

    for (let k = r + 1; k <= m; k++) {
        U[k - t] = U[k];
    }

    let j = fout, i = j;
    for (let k = 1; k < t; k++) {
        if (k % 2 === 1) {
            i++;
        } else {
            j--;
        }
    }

    for (let k = i + 1; k <= n; k++) {
        Pw[j] = Pw[k];
        j++;
    }
}

// Example usage of ALGORITHM A5.8
// let n, p, U, Pw, u, r, s, num;
// Initialize these variables as per your curve specifications
// RemoveCurveKnot(n, p, U, Pw, u, r, s, num);
// The control points Pw and knot vector U are modified in place

// Helper function: Distance4D (Point1, Point2)
// This function should calculate the 4D Euclidean distance between two points.
function Distance4D(Point1, Point2) {
    let dx = Point1[0] - Point2[0];
    let dy = Point1[1] - Point2[1];
    let dz = Point1[2] - Point2[2];
    let dw = Point1[3] - Point2[3];
    return Math.sqrt(dx * dx + dy * dy + dz * dz + dw * dw);
}


const TOL = 0.001; // Tolerance for knot removal















// ALGORITHM A5.9
// DegreeElevateCurve: Algorithm for degree elevation of a NURBS curve.
// This function increases the degree of a given NURBS curve by a factor of 't'.
// Input: n (number of control points minus one), p (degree of the curve), 
//        U (knot vector), Pw (control points), t (degree elevation factor)
// Output: Returns an object containing the new degree (nh), the new knot vector (Uh),
//         and the new control points (Qw) of the elevated curve.
function DegreeElevateCurve(n, p, U, Pw, t) {
    let m = n + p + 1;
    let ph = p + t;
    let bezalfs = new Array(ph + 1).fill(0).map(() => new Array(p + 1).fill(0));
    let bpts = new Array(p + 1);
    let ebpts = new Array(ph + 1);
    let nextbpts = new Array(p - 1);
    let alfs = new Array(p - 1);
    let mh = ph;
    let r = -1;
    let a = p;
    let b = p + 1;
    let cind = 1;
    let ua = U[0];
    let Qw = new Array(m + t);
    let Uh = new Array(m + t);

    // Initialize bezalfs
    bezalfs[0][0] = bezalfs[ph][p] = 1.0;
    for (let i = 1; i <= ph; i++) {
        let mpi = Math.min(p, i);
        for (let j = Math.max(0, i - t); j <= mpi; j++) {
            bezalfs[i][j] = Bin(ph, i) * Bin(p, j) * Bin(t, i - j) / Bin(ph, j);
        }
    }

    // Initialize first bezier seg
    for (let i = 0; i <= p; i++) {
        bpts[i] = Pw[i];
    }

    // Big loop through knot vector
    while (b < m) {
        i = b;
        while (b < m && U[b] === U[b + 1]) {
            b++;
        }
        let mul = b - i + 1;
        mh += mul + t;
        let ub = U[b];
        let oldr = r;
        r = p - mul;

        // Insert knot u(b) r times
        if (oldr > 0) {
            lbz = Math.floor((oldr + 2) / 2);
        } else {
            lbz = 1;
        }

        if (r > 0) {
            rbz = ph - Math.floor((r + 1) / 2);
        } else {
            rbz = ph;
        }

        if (r > 0) {
            // Insert knot to get Bézier segment
            let numer = ub - ua;
            for (let k = p; k > mul; k--) {
                alfs[k - mul - 1] = numer / (U[a + k] - ua);
            }

            for (let j = 1; j <= r; j++) {
                let save = r - j;
                let s = mul + j;
                for (let k = p; k >= s; k--) {
                    bpts[k] = alfs[k - s] * bpts[k] + (1.0 - alfs[k - s]) * bpts[k - 1];
                }
                nextbpts[save] = bpts[p];
            }
        }

        if (r > 0) {
            let numer = ub - ua;
            for (let k = p; k > mul; k--) {
                alfs[k - mul - 1] = numer / (U[a + k] - ua);
            }

            for (let j = 1; j <= r; j++) {
                let save = r - j;
                let s = mul + j;

                for (let k = p; k >= s; k--) {
                    bpts[k] = alfs[k - s] * bpts[k] + (1.0 - alfs[k - s]) * bpts[k - 1];
                }
                nextbpts[save] = bpts[p];
            }
        }




        // Degree elevate Bezier
        for (let i = lbz; i <= ph; i++) {
            ebpts[i] = 0.0;
            let mpi = Math.min(p, i);
            for (let j = Math.max(0, i - t); j <= mpi; j++) {
                ebpts[i] += bezalfs[i][j] * bpts[j];
            }
        }

        // Prepare for next pass through loop
        if (oldr > 1) {
            let lbz = Math.max(2, lbz);
            for (let i = lbz; i <= ph; i++) {
                let ii = i - lbz;
                Qw[cind + ii] = ebpts[i];
                Uh[cind + ii] = ub;
            }
            for (let i = 0; i < ph - oldr; i++) {
                bpts[i] = nextbpts[i];
            }
            for (let i = ph - oldr; i < ph; i++) {
                bpts[i] = Pw[b - ph + i];
            }
            a = b;
            b++;
            ua = ub;
        }


        if (a !== p) {
            for (let i = 0; i < ph - oldr; i++) {
                Uh[kind++] = ua;
            }
            for (let i = lbz; i <= ph; i++) {
                ebpts[i] = Pw[a - ph + i];
            }
            b = b + 1;
            if (b < m) {
                ua = U[b];
            }
            else {
                ua = U[b + 1];
            }
            a = b;
            for (let i = 0; i <= ph; i++) {
                bpts[i] = ebpts[i];
            }
        }

        for (let j = lbz; j <= rbz; j++) {
            Qw[cind++] = ebpts[j];
        }

        if (b < m) {
            // Set up for next pass through loop
            for (let i = 0; i <= ph - oldr - 1; i++) {
                bpts[i] = nextbpts[i];
            }
            for (let i = ph - oldr; i <= ph; i++) {
                bpts[i] = Pw[b - ph + i];
            }
            a = b;
            b++;
            if (b < m) ua = U[b];
        } else {
            // End knot
            for (let i = 0; i <= ph; i++) {
                Uh[kind + i] = ub;
            }
        }


        first = first - 1;
        last = last + 1;
    }

    // Finish the last bezier seg
    for (let i = 0; i <= ph; i++) {
        Uh[kind + i] = U[b];
    }

    return { nh: mh - ph - 1, Uh, Qw };
}




// Example usage of DegreeElevateCurve
// let n = /* number of control points minus one */;
// let p = /* degree of the curve */;
// let U = /* original knot vector */;
// let Pw = /* control points */;
// let t = /* number of times to elevate degree */;
// let { nh, Uh, Qw } = DegreeElevateCurve(n, p, U, Pw, t);
// console.log('New degree:', nh);
// console.log('New knot vector:', Uh);
// console.log('New control points:', Qw);







// ALGORITHM A5.10
// DegreeElevateSurface: Algorithm for degree elevation of a NURBS surface.
// This function increases the degree of a given NURBS surface in either the U or V direction.
// Input: n, p, U, m, q, V, Pw, dir, t
// Output: nh, Uh, mh, Vh, Qw

function DegreeElevateSurface(n, p, U, m, q, V, Pw, dir, t) {
    // Assuming constants for directions
    const U_DIRECTION = 0;
    const V_DIRECTION = 1;

    let nh, Uh, mh, Vh, Qw; // Output variables

    if (dir === U_DIRECTION) {
        let Bezier = new Array(p + 1).fill(null).map(() => new Array(q + 1));
        let NextBezier = new Array(p + 1).fill(null).map(() => new Array(q + 1));
        let alphas = new Array(p + 1);
        let mh = p;
        let a = p;
        let b = p + 1;
        let Qw = new Array((n + t + 1) * (m + 1)).fill(null).map(() => new Array(4)); // Assuming 4D points
        let Uh = new Array(n + t + 1);

        // Initialize knot vectors and first row of control points
        for (let j = 0; j <= p; j++) {
            Uh[j] = U[j];
        }
        for (let i = 0; i <= n; i++) {
            Qw[i][0] = Pw[i][0];
        }

        let kind = p + 1;
        let ua = U[0];
        let ub = 0;
        let r = 0;

        // Main loop through knot vector
        while (b < m) {
            // get multiplicity, ub, r, oldr, etc.
            ub = U[b];
            while (b < m && U[b] === ub) {
                b++;
            }
            let oldr = r;
            r = p - (b - a);

            // Save alfas
            for (let i = 0; i <= p - oldr - 1; i++) {
                alphas[i] = ub - ua;
            }
            for (let j = 0; j <= p; j++) {
                Bezier[j] = Pw[a - p + j];
            }

            // Insert knot
            if (oldr > 0) {
                let first = kind - 2;
                let last = kind;
                let den = ub - ua;
                let bet = (ub - Uh[kind - 1]) / den;

                for (; last - first > 0; last--, first++) {
                    for (let i = 0; i <= p; i++) {
                        Bezier[i] = alphas[i] * (Bezier[i] - NextBezier[first][i]) / bet + NextBezier[first][i];
                    }
                    Qw[kind][0] = Bezier[p];
                    kind++;
                }
            }

            if (a !== p) {
                for (let i = 0; i < p - r; i++) {
                    Qw[kind][0] = Bezier[i];
                    kind++;
                }
            }

            if (b < m) {
                for (let i = 0; i <= r; i++) {
                    Bezier[i] = Pw[b - r + i];
                }
                a = b;
                b++;
                ua = ub;
            } else {
                for (let i = 0; i <= p; i++) {
                    Qw[kind + i][0] = Bezier[i];
                }
            }
        }

        // Update remaining control points and knots
        for (let i = kind; i <= mh; i++) {
            Uh[i] = ub;
        }
        for (let i = mh + 1; i <= ph; i++) {
            Uh[i] = U[m];
        }
        for (let j = 0; j <= q; j++) {
            for (let i = mh - p; i <= n + t; i++) {
                Qw[i][j] = Pw[a - p + i][j];
            }
        }

    } else if (dir === V_DIRECTION) {
        let Bezier = new Array(q + 1).fill(null).map(() => new Array(n + 1));
        let NextBezier = new Array(q + 1).fill(null).map(() => new Array(n + 1));
        let alphas = new Array(q + 1);
        let mh = q;
        let a = q;
        let b = q + 1;
        let Qw = new Array((m + t + 1) * (n + 1)).fill(null).map(() => new Array(4)); // Assuming 4D points
        let Vh = new Array(m + t + 1);

        for (let j = 0; j <= q; j++) {
            Vh[j] = V[j];
        }
        for (let i = 0; i <= m; i++) {
            for (let j = 0; j <= n; j++) {
                Qw[j][i] = Pw[j][i];
            }
        }

        let kind = q + 1;
        let va = V[0];
        let vb = 0;
        let r = 0;

        while (b < m) {
            vb = V[b];
            while (b < m && V[b] === vb) {
                b++;
            }
            let oldr = r;
            r = q - (b - a);

            for (let i = 0; i <= q - oldr - 1; i++) {
                alphas[i] = vb - va;
            }
            for (let j = 0; j <= q; j++) {
                Bezier[j] = Pw[a - q + j];
            }

            if (oldr > 0) {
                let first = kind - 2;
                let last = kind;
                let den = vb - va;
                let bet = (vb - Vh[kind - 1]) / den;

                for (; last - first > 0; last--, first++) {
                    for (let i = 0; i <= q; i++) {
                        Bezier[i] = alphas[i] * (Bezier[i] - NextBezier[first][i]) / bet + NextBezier[first][i];
                    }
                    for (let j = 0; j <= n; j++) {
                        Qw[j][kind] = Bezier[q];
                    }
                    kind++;
                }
            }

            if (a !== q) {
                for (let i = 0; i < q - r; i++) {
                    for (let j = 0; j <= n; j++) {
                        Qw[j][kind] = Bezier[i];
                    }
                    kind++;
                }
            }

            if (b < m) {
                for (let i = 0; i <= r; i++) {
                    Bezier[i] = Pw[b - r + i];
                }
                a = b;
                b++;
                va = vb;
            } else {
                for (let i = 0; i <= q; i++) {
                    for (let j = 0; j <= n; j++) {
                        Qw[j][kind + i] = Bezier[i];
                    }
                }
            }
        }

        for (let i = kind; i <= mh; i++) {
            Vh[i] = vb;
        }
        for (let i = mh + 1; i <= ph; i++) {
            Vh[i] = V[m];
        }
        for (let i = 0; i <= n; i++) {
            for (let j = mh - q; j <= m + t; j++) {
                Pw[i][j] = Qw[i][j];
            }
        }
    }


    return { nh, Uh, mh, Vh, Qw };
}

// Example usage of ALGORITHM A5.10
// let n, p, U, m, q, V, Pw, dir, t;
// Initialize these variables as per your surface specifications
// let result = DegreeElevateSurface(n, p, U, m, q, V, Pw, dir, t);
// Use result.nh, result.Uh, result.mh, result.Vh, result.Qw as needed






// ALGORITHM A5.11
// DegreeReduceCurve: Algorithm for degree reduction of a NURBS curve.
// This function attempts to reduce the degree of a NURBS curve from 'p' to 'p-1'.
// Input: n (number of control points minus one), p (degree of the curve),
//        U (original knot vector), Qw (original control points).
// Output: Returns an object containing the new degree (nh), the new knot vector (Uh),
//         and the new control points (Pw) of the degree-reduced curve.
function DegreeReduceCurve(n, p, U, Qw) {
    let ph = p - 1;
    let mh = ph;
    let kind = ph + 1;
    let r = -1;
    let a = p;
    let b = p + 1;
    let cind = 1;
    let mult = p;
    let m = n + p + 1;
    let Pw = new Array(n).fill(0).map(() => new Array(4)); // Assuming 4D points
    let Uh = new Array(m - 1);
    let MaxErr = 0;


    Pw[0] = Qw[0];
    for (let i = 0; i <= ph; i++) {
        Uh[i] = U[0]; // Compute left end of knot vector
    }

    let bpts = new Array(p + 1); // Initialize bpts array
    let rbpts = new Array(p + 1); // Initialize rbpts array
    let alphas = new Array(p - 1); // Initialize alphas array
    let Nextbpts = new Array(p - 1); // Initialize Nextbpts array
    let e = new Array(m).fill(0.0); // Initialize error vector

    // Main loop through knot vector
    while (b < m) {
        let i = b;
        while (b < m && U[b] === U[b + 1]) {
            b++;
        }
        mult = b - i + 1;
        mh = mh + mult - 1;
        let oldr = r;
        r = p - mult;

        // Degree reduction steps
        for (let i = 0; i <= p; i++) {
            bpts[i] = Qw[a - p + i];
        }
        for (let i = 0; i <= p - 1; i++) {
            rbpts[i] = bpts[i + 1];
        }

        for (let iter = 1; iter <= r; iter++) {
            let first = kind - 2;
            let last = kind;
            let den = U[b] - U[a];
            for (let i = first; i < last; i++) {
                alphas[i - first] = (U[b] - Uh[i]) / den;
                for (let dim = 0; dim < 4; dim++) {
                    rbpts[i] = alphas[i - first] * rbpts[i] + (1.0 - alphas[i - first]) * rbpts[i + 1];
                }
            }
            kind++;
        }

        // Compute the error of degree reduction at each step
        for (let i = a; i <= b; i++) {
            e[i] = 0.0;
            for (let dim = 0; dim < 4; dim++) {
                e[i] += Math.pow(Qw[i][dim] - rbpts[kind - a + ph - i][dim], 2);
            }
            e[i] = Math.sqrt(e[i]);
            MaxErr = Math.max(MaxErr, e[i]);
        }


        // Check if curve is degree reducible
        if (e[a] > TOL) {
            console.log("Curve not degree reducible");
            return;
        }

        // Knot removal and error bounds computation
        if (oldr > 0) {
            let first = kind - 2;
            let last = kind;
            for (let i = first; i < last; i++) {
                for (let j = 0; j < 4; j++) {  // Assuming 4D points
                    Pw[cind][j] = rbpts[i - first][j];
                }
                Uh[cind] = U[a];
                cind++;
            }
        } else if (a !== p) {
            for (let i = 0; i < 4; i++) {  // Assuming 4D points
                Pw[cind][i] = Qw[a][i];
            }
            Uh[cind] = U[a];
            cind++;
        }

        // Set up for next iteration
        a++;
        if (a < m) {
            for (let i = 0; i < p - mult; i++) {
                bpts[i] = Qw[a - p + mult + i];
            }
            for (let i = 0; i < mult; i++) {
                rbpts[i] = Qw[a + i];
            }
        }

        // Update variables a, b, etc. for the next pass through the loop
    }

    nh = mh - ph - 1;
    return { nh, Uh, Pw }; // Return the new degree, knot vector, and control points
}

// Example usage of DegreeReduceCurve
// let n = /* number of control points minus one */;
// let p = /* degree of the curve */;
// let U = /* original knot vector */;
// let Qw = /* control points */;
// let { nh, Uh, Pw } = DegreeReduceCurve(n, p, U, Qw);







//---------------------Chapter 6: Advanced Geometric Algorithms 

// ALGORITHM A6.1
// BezierToPowerMatrix: Algorithm for computing the matrix to convert Bézier form to power form.
// This function calculates the matrix used to convert a curve from its Bézier form to the power form.
// Input: p (degree of the Bézier curve)
// Output: Returns a matrix that can be used to convert the Bézier form of a curve of degree 'p' to its power form.
function BezierToPowerMatrix(p) {
    let M = new Array(p + 1).fill(0).map(() => new Array(p + 1).fill(0));
    for (let i = 0; i <= p; i++) {
        for (let j = i + 1; j <= p; j++) {
            M[i][j] = 0.0;
        }
    }

    M[0][0] = M[p][p] = 1.0;
    M[p][0] = (p % 2 === 0) ? 1.0 : -1.0;
    let sign = -1.0;

    for (let i = 1; i < p; i++) {
        M[i][i] = Bin(p, i);
        M[i][0] = M[p][p - i] = sign * M[i][i];
        sign = -sign;
    }

    let k1 = Math.floor((p + 1) / 2);
    let pk = p - 1;
    for (let k = 1; k < k1; k++) {
        sign = -1.0;
        for (let j = k + 1; j <= pk; j++) {
            M[j][k] = M[pk][p - j] = sign * Bin(p, k) * Bin(p - k, j - k);
            sign = -sign;
        }
        pk--;
    }

    return M;
}
// Example usage of BezierToPowerMatrix
// let p = /* degree of the Bézier curve */;
// let matrix = BezierToPowerMatrix(p);
// Use 'matrix' for converting Bézier form to power form





// ALGORITHM A6.2
// PowerToBezierMatrix: Algorithm for computing the matrix to convert power form to Bézier form.
// This function calculates the matrix used to convert a curve from its power form to the Bézier form.
// Input: p (degree of the curve), M (matrix to be inverted)
// Output: Returns the inverse matrix that can be used to convert the power form of a curve of degree 'p' to its Bézier form.
function PowerToBezierMatrix(p, M) {
    let MI = new Array(p + 1).fill(0).map(() => new Array(p + 1).fill(0));

    for (let i = 0; i < p; i++) {
        for (let j = i + 1; j <= p; j++) {
            MI[i][j] = 0.0;
        }
    }

    for (let i = 0; i <= p; i++) {
        MI[i][0] = MI[p][i] = 1.0;
        MI[i][i] = 1.0 / M[i][i];
    }

    let k1 = Math.floor((p + 1) / 2), pk = p - 1;
    for (let k = 1; k < k1; k++) {
        for (let j = k + 1; j <= pk; j++) {
            let d = 0.0;
            for (let i = k; i < j; i++) {
                d -= M[j][i] * MI[i][k];
            }
            MI[j][k] = d / M[j][j];
            MI[pk][p - j] = MI[j][k];
        }
        pk--;
    }

    return MI;
}
// Example usage of PowerToBezierMatrix
// let p = /* degree of the curve */;
// let M = /* matrix from Bézier to power form (from A6.1) */;
// let MI = PowerToBezierMatrix(p, M);
// Use 'MI' for converting power form to Bézier form



//---------------------Chapter 7: Conics and Circles







//---------------------Chapter 8: Construction of Common Surfaces 



//---------------------Chapter 9: Curve and Surface Fitting 


//---------------------Chapter 10: Advanced Surface Construction Techniques