# pylookup

pylookup is a project for Python implementations of popular lookup arguments. We implemented lookup arguments below:

1. plookup: https://eprint.iacr.org/2020/315.pdf
2. Caulk+: https://eprint.iacr.org/2022/957.pdf
3. baloo: https://eprint.iacr.org/2022/1565.pdf
4. CQ: https://eprint.iacr.org/2022/1763.pdf
5. lasso: https://eprint.iacr.org/2023/1216.pdf
6. LogUp+GKR: https://eprint.iacr.org/2023/1284.pdf

Blog Posts
* [Blog Post of CQ](https://harryx1x1.fun/2024-01-23/cq-en/)
* [Blog Post of Plookup](https://github.com/NOOMA-42/pylookup/blob/main/src/plookup/Introduction.md)
* [Blog Post of Baloo](https://github.com/sec-bit/learning-zkp/tree/develop/lookup-arguments/baloo-en)

## Test
Navigate to specific lookup argument folder and execute with command such as:

```bash
$ poetry run python3 test.py
```

## Acknowledgement
- MLE, Sumcheck, GKR implementation credits to [gkr](https://github.com/jeong0982/gkr) by Soowon
- Folder `common_util` are modified based on [Plonkathon](https://github.com/0xPARC/plonkathon)
