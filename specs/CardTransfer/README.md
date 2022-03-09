# BankTransfer

This is a simplified distributed system coordination problem.

In this exercise, imagine we are a bank, and we are serving an API request from our banking mobile app to initiate a bank transfer from an external financial institution to the user's account.

 We are building a API endpoint that asks the other financial institution to move money over to us.
 
 The wrinkle here is that internally, the transfer also needs to be synchronized with a third, internal transaction database (our internal source of truth) to formally recognize the balance in the user's account.

 How do we design this system to ensure the design is resilient to failures and outages?
 

### Requirements:

- We must guarantee that balances are kept consistent between our system and the external institutions. No money should be lost/created on either side (obviously).
- The external service may fail to process the transaction for any reason (downtime, network partition, system error)
- The internal transaction service may also fail to process the transaction for any reason (antifraud rules, domain logic, ratelimiting, network partitions)
- The API request is synchronous, and must respond within 200ms @ p99

### The Happy Path

We illustrate the system design using the happy path. Our mobile client calls an API gateway, which we use as a transaction coordinator.

The API gateway makes 2 calls. First, it calls the external financial institution to initiate the transfer. If the transfer is successful, the API then turns around and pings the internal balance store service to note the transaction was a success.

(Note that this is not representative of a real world bank! This is a contrived, simplified example).

Because we need our API to be synchronous, the API coordinator blocks until both responses are success, before returning a success response to the client.

```mermaid
sequenceDiagram
autonumber
OurMobileClient->>+OurAPIGateway: ApproveTransfer
OurAPIGateway->>+ExternalFinancialInstitution: StartTransfer
ExternalFinancialInstitution->>-OurAPIGateway: SUCCESS
OurAPIGateway->>+OurInternalBalanceStore: UpdateUserBalance
OurInternalBalanceStore->>-OurAPIGateway: SUCCESS
OurAPIGateway->>-OurMobileClient: SUCCESS
```

### Internal API error with compensating transaction

Of course, we know that errors can crop up in the real world. If the call to either service borks, we will need a way to either retry or fail gracefully. Here, we consider the use case where our internal API service crashes.

We consult with the team and decide that if the API service crashes for any reason, we will want to undo the transaction in the external financial institution with a compensating transaction. We will throw this work onto an external queue as soon as an error occurs.

```mermaid
sequenceDiagram
autonumber
OurMobileClient->>+OurAPIGateway: ApproveTransfer
OurAPIGateway->>+ExternalFinancialInstitution: StartTransfer
ExternalFinancialInstitution->>-OurAPIGateway: SUCCESS
OurAPIGateway->>+OurInternalBalanceStore: UpdateUserBalance
OurInternalBalanceStore->>-OurAPIGateway: FAILED
OurAPIGateway--)BackgroundWorker: Enqueue Reversal
Note over OurAPIGateway,BackgroundWorker: Compensating transaction kicks off after a failure
OurAPIGateway->>-OurMobileClient: FAILED
BackgroundWorker->>+ExternalFinancialInstitution: UndoStartTransfer
ExternalFinancialInstitution->>-BackgroundWorker: SUCCESS
```

This should work, right?

## Enter formal specifications!

OK, let's try to model this behavior as a formal TLA+ spec.

