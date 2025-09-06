# Privacy Policy

We collect only the data needed to verify CI receipts and operate the GitHub App.
- Inputs: workflow metadata (repository, workflow_run id), the uploaded artifact named `tau-crystal-manifest`, and minimal account info for plan checks.
- Storage: a monthly usage counter keyed by account login (free/pro run counts). No source code is stored by this service.
- No selling or sharing of personal data. We don’t use tracking cookies or third-party ads.
- Security: webhooks are verified with an HMAC secret; the app uses GitHub App authentication; receipts are processed in-memory.
- Retention: usage counters reset monthly; logs rotate routinely.
Contact: open a private security advisory for sensitive issues, or a Discussion/Issue for general questions.
