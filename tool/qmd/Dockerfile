FROM oven/bun:1

RUN apt-get update \
    && apt-get install -y --no-install-recommends python3 make g++ socat \
    && rm -rf /var/lib/apt/lists/*

RUN bun install -g @tobilu/qmd

WORKDIR /workspace/docs

ENTRYPOINT ["sh", "-lc"]
CMD ["bun /root/.bun/install/global/node_modules/@tobilu/qmd/dist/cli/qmd.js mcp --http --port 8182 & QMD_PID=$!; socat TCP-LISTEN:8181,bind=0.0.0.0,reuseaddr,fork TCP6:[::1]:8182 & SOCAT_PID=$!; trap 'kill $QMD_PID $SOCAT_PID 2>/dev/null || true' INT TERM EXIT; while kill -0 $QMD_PID 2>/dev/null && kill -0 $SOCAT_PID 2>/dev/null; do sleep 1; done; exit 1"]
