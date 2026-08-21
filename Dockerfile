# proofs.hanzo.ai — the machine-checked-proof index, served by the Hanzo native
# static server. Two stages, one image, no runtime Node.
#
#   1. build — npm ci + next build; next.config.mjs sets output:'export' and
#              trailingSlash:true, so the export is already a directory tree
#              (out/<page>/index.html) and hanzoai/static resolves every route
#              with zero redirects. next/font/google is inlined into
#              _next/static/media at build time, so the served page fetches
#              nothing off-origin.
#   2. serve — ghcr.io/hanzoai/static (scratch + one Go binary) on :3000. CSP is
#              widened for the export's own JS via HANZO_STATIC_CSP, set on the
#              operator CR (universe crs/proofs.yaml).
#
# The site lives in site/; the build context is the repo root so the LaTeX/Lean
# sources stay out of the image. The PDFs at the repo root are deliberately NOT
# copied — the image serves the index, not the paper archive.
#
# Build (in-cluster, POST /v1/runner — no GitHub builders):
#   {"repo":"https://github.com/hanzoai/proofs","image":"ghcr.io/hanzoai/proofs:<tag>"}

FROM node:22-slim AS build
WORKDIR /app
COPY site/package.json site/package-lock.json ./
RUN npm ci
COPY site/ ./
ENV NODE_OPTIONS=--max-old-space-size=4096
RUN npm run build

# v0.5.1 answered `max-age=86400` to every request, the document included, so a
# browser that had seen this site once did not ask again for a day and the next
# publish reached nobody — indistinguishable from a deploy that failed. v0.5.8 is
# where the policy arrived that tells the two apart: content-addressed `_next/`
# assets immutable, the document `no-cache`.
FROM ghcr.io/hanzoai/static:v0.5.9
COPY --from=build /app/out /public
