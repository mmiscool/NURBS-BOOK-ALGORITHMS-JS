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









