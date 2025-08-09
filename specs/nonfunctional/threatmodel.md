# Threat Model

## System Overview
The inventory reservation system manages stock allocation for orders.

## STRIDE Analysis

### Spoofing
- **Threat**: Unauthorized reservation creation
- **Mitigation**: API key authentication, rate limiting

### Tampering
- **Threat**: Modification of reservation data in transit
- **Mitigation**: TLS encryption, request signing

### Repudiation
- **Threat**: Denial of reservation creation
- **Mitigation**: Audit logging, event sourcing

### Information Disclosure
- **Threat**: Exposure of inventory levels to competitors
- **Mitigation**: Access control, data classification

### Denial of Service
- **Threat**: Exhausting inventory through fake reservations
- **Mitigation**: Rate limiting, reservation timeouts

### Elevation of Privilege
- **Threat**: Regular user accessing admin functions
- **Mitigation**: Role-based access control, principle of least privilege