using EntryPointMock as entry;
using SimpleReentrantPaymaster as reentrant;

methods {
    /// IERC1822ProxiableUpgradeable
    function _.proxiableUUID() external => ERC1822ProxiableUUID(calledContract) expect bytes32;

    function owner() external returns (address) envfree;
    function entryPoint() external returns (address) envfree;
    function balances(address) external returns (uint256) envfree;
    function contractSpent(address) external returns (uint256) envfree;
    function unlockBlock(address) external returns (uint256) envfree;
    function MAX_COST_OF_USEROP() external returns (uint256) envfree;

    function rateLimit(address,address) external returns (uint256,uint256,uint256) envfree;
    function costLimit(address,address) external returns (uint256,uint256,uint256) envfree;
    function totalRateLimit(address) external returns (uint256,uint256,uint256) envfree;

    function depositInfo(address) external returns (uint256,uint256) envfree;
    function getDeposit() external returns (uint256) envfree;
    function appUserLimit(address,address) external returns (uint256,uint256,uint256,uint256) envfree;

    function entry.decodeContext(bytes) external returns (address,address,uint256) envfree;
}

/*struct RateLimitData {
    uint256 lastOperationTime;
    uint256 operationCount;
    uint256 ethCostCount;
}*/

function contextDecode(bytes context) returns (address, address, uint256) {
    address account; address user; uint256 gasPrice;
    account, user, gasPrice = entry.decodeContext(context);
    return (account, user, gasPrice);
}

persistent ghost ERC1822ProxiableUUID(address) returns bytes32;
persistent ghost bool reentrantWasCalled;

definition upgradeMethods(method f) returns bool = 
    f.selector == sig:upgradeToAndCall(address,bytes).selector;

definition viewOrUpgrade(method f) returns bool = upgradeMethods(f) || f.isView;

definition senderIsSelf(env e) returns bool = e.msg.sender == currentContract;

// Hooking on low-level call.
hook CALL(uint g, address addr, uint value, uint argsOffset, uint argsLength, uint retOffset, uint retLength) uint rc {
    /// Equivalent to require success for empty calldata:
    /// Every fallback returns success = true.
    require argsLength == 0 => rc == 1;
    if(addr == reentrant) {
        reentrantWasCalled = true;
    }
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Ghost & hooks: sum of all balances                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/
ghost mapping(address => bool) accessedUser;
ghost mathint sumOfUserBalances_init {init_state axiom sumOfUserBalances_init == 0;}
ghost mathint sumOfUserBalances {init_state axiom sumOfUserBalances == 0;}
definition excludeFromSum(address account) returns bool = false;//account == currentContract;

hook Sload uint256 balance balances[KEY address user] STORAGE {
    if(!accessedUser[user] && !excludeFromSum(user)) {
        accessedUser[user] = true;
        sumOfUserBalances_init = sumOfUserBalances_init - balance;
        require sumOfUserBalances_init >=0;
    }
}

hook Sstore balances[KEY address user] uint256 balance_new (uint256 balance_old) STORAGE {
    if(!excludeFromSum(user)) {
        sumOfUserBalances = sumOfUserBalances + balance_new - balance_old;
    }
}

function initializeSumOfBalances() {
    require sumOfUserBalances == sumOfUserBalances_init;
    require forall address user. !accessedUser[user];
}
