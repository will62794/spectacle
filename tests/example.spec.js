// @ts-check
import { test, expect } from '@playwright/test';

// test('has title', async ({ page }) => {
//   await page.goto('https://playwright.dev/');

//   // Expect a title "to contain" a substring.
//   await expect(page).toHaveTitle(/Playwright/);
// });

// test('get started link', async ({ page }) => {
//   await page.goto('https://playwright.dev/');

//   // Click the get started link.
//   await page.getByRole('link', { name: 'Get started' }).click();

//   // Expects page to have a heading with the name of Installation.
//   await expect(page.getByRole('heading', { name: 'Installation' })).toBeVisible();
// });

test('two-phase-basic', async ({ page }) => {
    await page.goto('http://127.0.0.1:8000/#!/home?specpath=./specs/TwoPhase.tla');
  
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
