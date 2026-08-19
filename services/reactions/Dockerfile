FROM --platform=$BUILDPLATFORM golang:1.24-alpine AS build
ARG TARGETOS
ARG TARGETARCH
WORKDIR /src
COPY go.mod go.sum ./
RUN go mod download
COPY *.go ./
RUN CGO_ENABLED=0 go test ./... \
    && CGO_ENABLED=0 GOOS=$TARGETOS GOARCH=$TARGETARCH go build -trimpath -ldflags="-s -w" -o /out/reactions .

FROM alpine:3.22
RUN apk add --no-cache ca-certificates \
    && addgroup -S -g 10001 reactions \
    && adduser -S -D -H -u 10001 -G reactions reactions
COPY --from=build /out/reactions /usr/local/bin/reactions
RUN mkdir -p /var/lib/reactions/backups && chown -R reactions:reactions /var/lib/reactions
USER reactions
EXPOSE 8081
ENTRYPOINT ["/usr/local/bin/reactions"]
