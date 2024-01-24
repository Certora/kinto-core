import "setup.spec";
import "../Initializable.spec";

use rule cannotInitializeIfDisabled;
use invariant initializingIsDisabled filtered{f -> !upgradeMethods(f)}

/// @title The sum of user balances is covered by the EntryPoint deposit of the Paymaster.
invariant PaymasterEthSolvency()
    to_mathint(getDeposit()) >= sumOfUserBalances
    filtered{f -> !upgradeMethods(f)}
    {
        preserved with (env e) {
            require !senderIsSelf(e);
        }
    }

/// @title The gas cost post-op cannot depend on the user address.
/// The contract spent can only change for the post-op context account.
rule postOpGasCostIsUserFree() {
    env e;
    IPaymaster.PostOpMode modeA;
    IPaymaster.PostOpMode modeB;
    bytes contextA; uint256 priceA; address accountA; 
        accountA, _, priceA = contextDecode(contextA);
    bytes contextB;  uint256 priceB; address accountB;
        accountB, _, priceB = contextDecode(contextB);
    uint256 actualGasCost;
    storage initState = lastStorage;

    uint256 spentA_0 = contractSpent(accountA);
    uint256 spentB_0 = contractSpent(accountB);

    postOp(e, modeA, contextA, actualGasCost) at initState;
    uint256 spentA_1 = contractSpent(accountA);
    uint256 spentB_1 = contractSpent(accountB);
    
    postOp(e, modeB, contextB, actualGasCost) at initState;
    uint256 spentA_2 = contractSpent(accountA);
    uint256 spentB_2 = contractSpent(accountB);

    assert accountA != accountB => spentB_0 == spentB_1, "The contract spent gas could only change for the account";
    assert accountA != accountB => spentA_0 == spentA_2, "The contract spent gas could only change for the account";
    assert priceB == priceA => spentA_1 - spentA_0 == spentB_2 - spentB_0, 
        "If the gas price doesn't change between calls, then the spent amount shouldn't changed";
}

/// @title The balance of any account can only increase by addDepositFor().
rule balanceOnlyIncreasesByDeposit(address account, method f) filtered{f -> !viewOrUpgrade(f)} {
    reentrantWasCalled = false;
    uint256 balanceBefore = balances(account);
        env e;
        calldataarg args;
        f(e,args);
    uint256 balanceAfter = balances(account);

    assert !reentrantWasCalled => (balanceAfter > balanceBefore => f.selector == sig:addDepositFor(address).selector);
    assert reentrantWasCalled => (balanceBefore > balanceBefore => account == reentrant);
}

/// @title The balance of any account can decrease at most by the MAX_COST_OF_USEROP().
rule balanceDecreaseIsAtMostMaxOpCost(address account, method f) 
filtered{f -> !viewOrUpgrade(f) &&
    f.selector != sig:withdrawTokensTo(address,uint256).selector &&
    f.selector != sig:withdrawTo(address,uint256).selector} 
{    
    uint256 balanceBefore = balances(account);
        env e;
        calldataarg args;
        f(e,args);
    uint256 balanceAfter = balances(account);

    assert balanceAfter < balanceBefore => balanceBefore - balanceAfter <= to_mathint(MAX_COST_OF_USEROP());
}

/// @title No operation can front-run validatePaymasterUserOp() and make it revert.
rule noOperationFrontRunsValidate(method f) 
filtered{f -> !viewOrUpgrade(f) && f.selector != 
    sig:validatePaymasterUserOp(SponsorPaymaster.UserOperation,bytes32,uint256).selector} {
    
    env e1; calldataarg args1;
    env e2; calldataarg args2;
    storage initState = lastStorage;

    bytes context;
    context, _ = validatePaymasterUserOp(e1, args1) at initState;
    address app;
    app, _, _ = contextDecode(context);

    f(e2, args2) at initState;
    validatePaymasterUserOp@withrevert(e1, args1);
    bool reverted = lastReverted;

    if(f.selector == sig:postOp(IPaymaster.PostOpMode,bytes,uint256).selector) {
        assert e2.msg.sender == entryPoint();
    }
    else if(f.selector == sig:initialize(address).selector) {
        assert reverted => app == owner();
    }
    else if(f.selector == sig:unlockTokenDeposit().selector) {
        assert reverted => app == e2.msg.sender;
    }
    else {
        assert !reverted;
    }   

    assert true;
}

/// @title The operation count per app is updated correctly
rule operationsCountUpdatedCorrectly(address account, address app) {
    uint256 rateCount_before; _, rateCount_before, _ = rateLimit(account, app);
    uint256 cost_before; _, _, cost_before = costLimit(account, app);
    uint256 totalCount_before; _, totalCount_before, _ = totalRateLimit(account);
    mathint balance_before = balances(app);
        env e;
        bytes context; uint256 actualGasCost; IPaymaster.PostOpMode mode;
        postOp(e, mode, context, actualGasCost);
        uint256 time = e.block.timestamp;
    uint256 rateCount_after; _, rateCount_after, _ = rateLimit(account, app);
    uint256 cost_after; _, _, cost_after = costLimit(account, app);
    uint256 totalCount_after; _, totalCount_after, _ = totalRateLimit(account);
    mathint cost = balance_before - balances(app);

    address appA; address accountA; 
    appA, accountA, _ = contextDecode(context);

    if(account != accountA || app != appA) {
        assert rateCount_before == rateCount_after;
        assert cost_before == cost_after;
        if(account != accountA) {
            assert totalCount_before == totalCount_after;
        }
        else {
            assert totalCount_after - totalCount_before == 1 || totalCount_after == 1;
        }
    }
    else {
        assert rateCount_after - rateCount_before == 1 || rateCount_after == 1;
        assert cost_after - cost_before == cost || to_mathint(cost_after) == cost;
        assert totalCount_after - totalCount_before == 1 || totalCount_after == 1;
    }
}

/// @title No operation can change the context output of validatePaymasterUserOp(). 
rule validationContextIsConsistent(method f) 
filtered{f -> !f.isView && f.selector != 
    sig:validatePaymasterUserOp(SponsorPaymaster.UserOperation,bytes32,uint256).selector} {
    env e1; calldataarg args1;
    env e2; calldataarg args2;
    //require e1.msg.sender != e2.msg.sender;
    storage initState = lastStorage;
    bytes context1; uint256 data1;
    bytes context2; uint256 data2;

    context1, data1 = validatePaymasterUserOp(e1, args1) at initState;
    address account1; address userAccount1; uint256 gasPricePostOp1;
    account1, userAccount1, gasPricePostOp1 = contextDecode(context1);

    f(e2, args2) at initState;
    context2, data2 = validatePaymasterUserOp(e1, args1);
    address account2; address userAccount2; uint256 gasPricePostOp2;
    account2, userAccount2, gasPricePostOp2 = contextDecode(context2);

    assert data1 == data2, "No operation should alter the validation data";
    assert account1 == account2 && 
        userAccount1 == userAccount2 && 
        gasPricePostOp1 == gasPricePostOp2, "No operation should alter the validation context";
}

/// @title A call validatePaymasterUserOp() can never front-run another call to the same function and make it revert.
/// @notice The EntryPoint calls both validatePaymasterUserOp() and postOp() in the same flow. So we must batch these two calls
/// together to one operation, which we would like to verify that cannot be front-run.
rule validatePayMasterCannotFrontRunEachOther() {
    env e1;
    env e2;
    SponsorPaymaster.UserOperation userOp1;
    SponsorPaymaster.UserOperation userOp2;
    IPaymaster.PostOpMode mode;
    bytes32 userOpHash1;
    bytes32 userOpHash2;
    uint256 maxCost1;
    uint256 maxCost2;

    bytes context1; address account1; address sender1; uint256 actualCost1;
    bytes context2; address account2; address sender2; uint256 actualCost2;
    
    storage initState = lastStorage;
    /// First attempt (validate + postOp)
    context1, _ = validatePaymasterUserOp(e1, userOp1, userOpHash1, maxCost1) at initState;
    account1, sender1, _ = contextDecode(context1);
    postOp(e1, mode, context1, actualCost1);
    
    /// Second user (validate + postOp)
    context2, _ = validatePaymasterUserOp(e2, userOp2, userOpHash2, maxCost2) at initState;
    account2, sender2, _ = contextDecode(context2);
    postOp(e2, mode, context2, actualCost2);

    /// Currently we only consider different senders.
    /// If the apps are equal, then the total limit could be reached.
    require sender1 != sender2;

    /// First attempt - again (validate + postOp)
    validatePaymasterUserOp@withrevert(e1, userOp1, userOpHash1, maxCost1);
    bool validateReverted = lastReverted;
    postOp@withrevert(e1, mode, context1, actualCost1);
    bool postOpReverted = lastReverted;

    assert !(validateReverted || postOpReverted);
}

/// @title The rate, cost and total rate limits last operation time is never in the future.
rule lastOperationTimeIsInThePast(address account, address app, method f) 
filtered{f -> !viewOrUpgrade(f)} {
    uint256 rate_lastOp_before; rate_lastOp_before, _ , _ = rateLimit(account, app);
    uint256 cost_lastOp_before; cost_lastOp_before, _ , _ = costLimit(account, app);
    uint256 total_lastOp_before; total_lastOp_before, _ , _ = totalRateLimit(account);
        env e;
        calldataarg args;
        f(e, args);
        uint256 time = e.block.timestamp;
    uint256 rate_lastOp_after; rate_lastOp_after, _ , _ = rateLimit(account, app);
    uint256 cost_lastOp_after; cost_lastOp_after, _ , _ = costLimit(account, app);
    uint256 total_lastOp_after; total_lastOp_after, _ , _ = totalRateLimit(account);

    assert rate_lastOp_before <= time => rate_lastOp_after <= time;
    assert cost_lastOp_before <= time => cost_lastOp_after <= time;
    assert total_lastOp_before <= time => total_lastOp_after <= time;
}

/// @title The postOp() changes the user limits of the op input context (account and sender) only.
rule postOpUpdatesLimits() {
    env e;
    address sender; address account;
    uint256 count1; uint256 lastOpTime_rate1; uint256 ethCount1; uint256 lastOpTime_cost1;
    uint256 count2; uint256 lastOpTime_rate2; uint256 ethCount2; uint256 lastOpTime_cost2;
    
    count1, lastOpTime_rate1, ethCount1, lastOpTime_cost1 = appUserLimit(sender, account);

    IPaymaster.PostOpMode mode;
    bytes context;
    uint256 gasCost;
    address _account; address _sender;
    _account, _sender, _ = contextDecode(context);
    postOp(e, mode, context, gasCost);
    
    count2, lastOpTime_rate2, ethCount2, lastOpTime_cost2 = appUserLimit(sender, account);

    assert lastOpTime_rate1 != lastOpTime_rate2 => (sender == _sender && account == _account);
}

/// @title Any operation may change the contract spent amount and balance for one app at a time.
rule onlyOneAppBalanceChangeAtATime(method f) filtered{f -> !viewOrUpgrade(f)} {
    env e;
    calldataarg args;
    address app1; address app2;
    reentrantWasCalled = false;

    uint256 spent1_before = contractSpent(app1);
    uint256 balance1_before = balances(app1);
    uint256 spent2_before = contractSpent(app2);
    uint256 balance2_before = balances(app2);
        f(e, args);
    uint256 spent1_after = contractSpent(app1);
    uint256 balance1_after = balances(app1);
    uint256 spent2_after = contractSpent(app2);
    uint256 balance2_after = balances(app2);

    if(reentrantWasCalled) {
        assert balance1_before != balance1_after => app1 == reentrant;
    }
    else {
        assert (spent1_before != spent1_after && app1 != app2) => spent2_before == spent2_after;
        assert (balance1_before != balance1_after && app1 != app2) => balance2_before == balance2_after;
    }
    assert true;
}

/// @title The contract spent amount cannot decrease, and must increase by the same amount the balance of that contract decreases.
rule contractSpentMustDecreaseBalance(method f, address app) 
filtered{f -> !viewOrUpgrade(f)} {
    env e;
    calldataarg args;
    uint256 spentBefore = contractSpent(app);
    uint256 balanceBefore = balances(app);
        f(e, args);
    uint256 spentAfter = contractSpent(app);
    uint256 balanceAfter = balances(app);
    mathint totalSpent = spentAfter - spentBefore;

    assert totalSpent >=0, "Spent amount cannot decrease";
    assert totalSpent !=0 => balanceBefore - balanceAfter == totalSpent, 
        "The spent amount must be reducted from the app balance";
}

/// @title No operation can front-run and make a call to withdrawTokensTo() revert.
rule cannotDos_withdrawTokensTo(method f) 
filtered{f -> !viewOrUpgrade(f)} {
    env e1;
    require e1.block.number > 0;
    address target; uint256 amount;

    initializeSumOfBalances();
    requireInvariant PaymasterEthSolvency();

    env e2;
    require e2.block.number > 0;
    require e2.msg.sender != e1.msg.sender;
    calldataarg args;

    storage initState = lastStorage;
    withdrawTokensTo(e1, target, amount) at initState;

    f(e2, args) at initState;
    withdrawTokensTo@withrevert(e1, target, amount);
    bool reverted = lastReverted;

    if(f.selector == sig:postOp(IPaymaster.PostOpMode,bytes,uint256).selector) {
        assert e2.msg.sender == entryPoint();
    }
    else if(f.selector == sig:initialize(address).selector) {
        assert reverted => e1.msg.sender == owner();
    }
    else {
        assert e1.msg.sender != reentrant => !reverted;
    }
    assert true;   
}

/// @title the addDepositFor() function updates the depositInfo correctly.
rule addDepositForIntegrity(address account) {
    env e;
    address account_other;

    uint256 balanceBefore; uint256 unlockBlock_before;
    balanceBefore, unlockBlock_before = depositInfo(account_other);
    mathint sumOfUserBalances_before = sumOfUserBalances;
        addDepositFor(e, account);
    uint256 balanceAfter; uint256 unlockBlock_after;
    balanceAfter, unlockBlock_after = depositInfo(account_other);
    mathint sumOfUserBalances_after = sumOfUserBalances;

    if(account_other != account) {
        assert balanceAfter == balanceBefore;
        assert unlockBlock_after == unlockBlock_before;
    }
    else {
        assert balanceAfter - balanceBefore == to_mathint(e.msg.value);
        assert account == e.msg.sender => unlockBlock_after == 0;
        assert account != e.msg.sender => unlockBlock_after == unlockBlock_before;
    }
    assert sumOfUserBalances_after - sumOfUserBalances_before == to_mathint(e.msg.value);
}

/// @title Only the user (or the EntryPoint) can change his own limits.
rule onlyUserCanChangeHisParameters(address account, method f) 
filtered{f -> !viewOrUpgrade(f)} {
    address app;

    uint256 rate_lastOperationTime_before;
    uint256 rate_operationCount_before;
    uint256 rate_ethCostCount_before;
    uint256 cost_lastOperationTime_before;
    uint256 cost_operationCount_before;
    uint256 cost_ethCostCount_before;
    uint256 total_lastOperationTime_before;
    uint256 total_operationCount_before;
    uint256 total_ethCostCount_before;
    uint256 amount_before; uint256 unlockBlock_before;

    rate_lastOperationTime_before,
    rate_operationCount_before,
    rate_ethCostCount_before = 
        rateLimit(account,app);
    cost_lastOperationTime_before,
    cost_operationCount_before,
    cost_ethCostCount_before = 
        costLimit(account,app);
    total_lastOperationTime_before,
    total_operationCount_before,
    total_ethCostCount_before = 
        totalRateLimit(account);
    amount_before, unlockBlock_before = depositInfo(account);

    env e; require e.msg.sender != account;
    require e.block.number > 0;
    calldataarg args;
    f(e, args);

    uint256 rate_lastOperationTime_after;
    uint256 rate_operationCount_after;
    uint256 rate_ethCostCount_after;
    uint256 cost_lastOperationTime_after;
    uint256 cost_operationCount_after;
    uint256 cost_ethCostCount_after;
    uint256 total_lastOperationTime_after;
    uint256 total_operationCount_after;
    uint256 total_ethCostCount_after;
    uint256 amount_after; uint256 unlockBlock_after;

    rate_lastOperationTime_after,
    rate_operationCount_after,
    rate_ethCostCount_after = 
        rateLimit(account,app);
    cost_lastOperationTime_after,
    cost_operationCount_after,
    cost_ethCostCount_after = 
        costLimit(account,app);
    total_lastOperationTime_after,
    total_operationCount_after,
    total_ethCostCount_after = 
        totalRateLimit(account);
    amount_after, unlockBlock_after = depositInfo(account);
    
    if(e.msg.sender != entryPoint()) {
        assert rate_lastOperationTime_before == rate_lastOperationTime_after;
        assert rate_operationCount_before == rate_operationCount_after;
        assert rate_ethCostCount_before == rate_ethCostCount_after;
        assert cost_lastOperationTime_before == cost_lastOperationTime_after;
        assert cost_operationCount_before == cost_operationCount_after;
        assert cost_ethCostCount_before == cost_ethCostCount_after;
        assert total_lastOperationTime_before == total_lastOperationTime_after;
        assert total_operationCount_before == total_operationCount_after;
        assert total_ethCostCount_before == total_ethCostCount_after;
        assert amount_before <= amount_after, "No one can reduce the deposit amount of another";
    }
    
    if(f.selector == sig:initialize(address).selector) {
        assert unlockBlock_before != unlockBlock_after => account == owner();
    }
    else {
        assert account != reentrant => unlockBlock_before == unlockBlock_after;
    }
}
