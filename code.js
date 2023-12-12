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












//----------------Chapter 2 


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








//--------------------Chapter 3

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






//------------------Chapter 4




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

// Assuming the Bin function is defined like this:
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







//---------------------Chapter 5







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






