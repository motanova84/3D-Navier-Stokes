// ============================================================================
// src/kernels/atmosphere.cu
// QCAL-Balearic Phase 1 kernel scaffold
// ============================================================================

#include <cuda_runtime.h>
#include <math.h>

#define F0 141.7001f
#define ALPHA 0.05f
#define LAMBDA 0.01f
#define D_PSI 0.1f
#define PSI_REF 0.999999f
#define PSI_MAX 1.0f
#define PSI_MIN 0.0f

#define NX 167
#define NY 167
#define NZ 60
#define NXYZ (NX * NY * NZ)

__device__ inline int idx3d(int ix, int iy, int iz) {
    return iz * (NX * NY) + iy * NX + ix;
}

__device__ inline float clamp_value(float value, float min_value, float max_value) {
    return fmaxf(fminf(value, max_value), min_value);
}

extern "C" __global__ void qcal_evolution(
    float* __restrict__ psi,
    const float* __restrict__ forcing,
    const float* __restrict__ lap_psi,
    float dt
) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= NXYZ) return;

    float psi_value = psi[idx];
    float dpsi_dt = D_PSI * lap_psi[idx]
                  - LAMBDA * (psi_value - PSI_REF)
                  + ALPHA * forcing[idx];
    psi[idx] = clamp_value(psi_value + dt * dpsi_dt, PSI_MIN, PSI_MAX);
}

extern "C" __global__ void spectral_diagnostic(
    const float* __restrict__ psi,
    float* __restrict__ coherence,
    float* __restrict__ entropy,
    float* __restrict__ frequency_deviation
) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= NXYZ) return;

    float psi_value = psi[idx];
    coherence[idx] = psi_value;
    entropy[idx] = -psi_value * logf(psi_value + 1e-12f);
    frequency_deviation[idx] = (psi_value - PSI_REF) * F0;
}
