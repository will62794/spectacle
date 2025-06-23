// @ts-check
import { test, expect } from '@playwright/test';

// 
// Basic UI tests for the TLA+ explorer interface.
// 

test('two-phase-basic', async ({ page }) => {
    await page.goto('http://localhost:3000/#!/home?specpath=./specs/TwoPhase.tla');
  
    // Expect a title "to contain" a substring.
    // await expect(page).toHaveTitle(/Playwright/);
    await expect(page.getByText('Choose Initial State')).toBeVisible();

    let nextStateChoices;
    let stateChoice;
    let traceStates;

    nextStateChoices = page.getByTestId('next-state-choice');
    stateChoice = nextStateChoices.nth(0);
    await stateChoice.click();
    traceStates = page.getByTestId('trace-state-elem');

    // Should now have 1 states in the trace.
    await expect(traceStates).toHaveCount(1, { timeout: 2000 });

    nextStateChoices = page.getByTestId('action-choice-param');
    stateChoice = nextStateChoices.nth(0);
    await stateChoice.click();
    traceStates = page.getByTestId('trace-state-elem');

    // Should now have 2 states in the trace.
    await expect(traceStates).toHaveCount(2, { timeout: 2000 });
  });
  
  test('lockserver-basic', async ({ page }) => {
    await page.goto('http://localhost:3000/#!/home?specpath=./specs/lockserver.tla');
  
    // Expect a title "to contain" a substring.
    await expect(page.getByTestId('set-constant-config-button')).toBeVisible();

    let constServerInput = page.getByTestId('const-val-input-Server');
    await constServerInput.fill('{s1,s2}');

    let constClientInput = page.getByTestId('const-val-input-Client');
    await constClientInput.fill('{c1,c2}');

    // Set the constants.
    await page.getByTestId('set-constant-config-button').click();

    // Now we should be on the state selection pane.
    await expect(page.getByText('Choose Initial State')).toBeVisible();

    let nextStateChoices;
    let stateChoice;
    let traceStates;

    nextStateChoices = page.getByTestId('next-state-choice');
    // Expect 1 initial state.
    await expect(nextStateChoices).toHaveCount(1, { timeout: 2000 });
    stateChoice = nextStateChoices.nth(0);
    await stateChoice.click();
    traceStates = page.getByTestId('trace-state-elem');

    // Should now have 1 states in the trace.
    await expect(traceStates).toHaveCount(1, { timeout: 2000 });

    nextStateChoices = page.getByTestId('action-choice-param');
    // Expect 4 distinct enabled actions.
    await expect(nextStateChoices).toHaveCount(4, { timeout: 2000 });

    // Find the action choice with text "c1"
    const c1s2Choice = nextStateChoices.filter({ hasText: 'c1' }).filter({ hasText: 's2' });
    await expect(c1s2Choice).toHaveCount(1);
    await c1s2Choice.nth(0).click();
    traceStates = page.getByTestId('trace-state-elem');

    // Should now have 2 states in the trace.
    await expect(traceStates).toHaveCount(2, { timeout: 2000 });

    // TODO: Checking actual state values.
    // await expect(traceStates.nth(1)).toHaveText('s2');
    // await expect(traceStates.nth(1)).toHaveText('FALSE');
  });

test('reset-trace-functionality', async ({ page }) => {
    await page.goto('http://localhost:3000/#!/home?specpath=./specs/TwoPhase.tla');
  
    // Wait for the initial state selection to be visible
    await expect(page.getByText('Choose Initial State')).toBeVisible();

    let nextStateChoices;
    let stateChoice;
    let traceStates;

    // Step 1: Choose initial state
    nextStateChoices = page.getByTestId('next-state-choice');
    stateChoice = nextStateChoices.nth(0);
    await stateChoice.click();
    traceStates = page.getByTestId('trace-state-elem');

    // Should now have 1 state in the trace
    await expect(traceStates).toHaveCount(1, { timeout: 2000 });

    // Step 2: Take first step forward
    nextStateChoices = page.getByTestId('action-choice-param');
    stateChoice = nextStateChoices.nth(0);
    await stateChoice.click();
    traceStates = page.getByTestId('trace-state-elem');

    // Should now have 2 states in the trace
    await expect(traceStates).toHaveCount(2, { timeout: 2000 });

    // Step 3: Take second step forward
    nextStateChoices = page.getByTestId('action-choice-param');
    stateChoice = nextStateChoices.nth(0);
    await stateChoice.click();
    traceStates = page.getByTestId('trace-state-elem');

    // Should now have 3 states in the trace
    await expect(traceStates).toHaveCount(3, { timeout: 2000 });

    // Step 4: Click the Reset button
    await page.getByTestId('trace-reset-button').click();

    // Step 5: Verify that the trace is now empty (back to initial state selection)
    await expect(page.getByText('Choose Initial State')).toBeVisible();
    
    // Verify that there are no trace states
    traceStates = page.getByTestId('trace-state-elem');
    await expect(traceStates).toHaveCount(0, { timeout: 2000 });
});

// let si_url_params = 'specpath=./specs/SnapshotIsolation.tla&constants%5BtxnIds%5D=%7Bt0%2Ct1%2Ct2%7D&constants%5Bkeys%5D=%7Bk1%2Ck2%7D&constants%5Bvalues%5D=%7Bv1%2Cv2%7D&constants%5BEmpty%5D="Empty"'
// test('snapshot-isolation-basic', async ({ page }) => {
//     await page.goto('http://127.0.0.1:8000/#!/home?' + si_url_params);
  
//     // Expect a title "to contain" a substring.
//     // await expect(page).toHaveTitle(/Playwright/);
//     await expect(page.getByText('Choose Initial State')).toBeVisible();

//     let nextStateChoices;
//     let stateChoice;
//     let traceStates;

//     nextStateChoices = page.getByTestId('next-state-choice');
//     stateChoice = nextStateChoices.nth(0);
//     await stateChoice.click();
//     traceStates = page.getByTestId('trace-state-elem');

//     // Should now have 1 states in the trace.
//     await expect(traceStates).toHaveCount(1, { timeout: 2000 });

//     nextStateChoices = page.getByTestId('action-choice-param');
//     stateChoice = nextStateChoices.nth(0);
//     await stateChoice.click();
//     traceStates = page.getByTestId('trace-state-elem');

//     // Should now have 2 states in the trace.
//     await expect(traceStates).toHaveCount(2, { timeout: 2000 });
//   });
