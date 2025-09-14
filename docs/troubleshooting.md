# Troubleshooting

- **nvidia-smi not found**: Reboot after `install/bootstrap.sh`. If Secure Boot is enabled, enroll MOK for NVIDIA.
- **torch.cuda.is_available() == False**: Verify driver & matching cu12x wheel; run `tools/gpu_diag.sh` and `tools/torch_diag.py`.
