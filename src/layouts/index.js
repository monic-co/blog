import React from 'react'
import Link from 'gatsby-link'
import { fontFace, injectGlobal } from "emotion"
import styled from "react-emotion"

injectGlobal`
  * {
    margin: 0;
    padding: 0;
    box-sizing: border-box;
  }

  body {
    background-color: #f4f5f6;
    color: #0a2e6b;
    font-family: proxima-nova, Nunino, sans-serif;
  }

  h2, h3 {
    font-weight: 300;
    margin: 60px 0 30px;
  }

  p, ul {
    font-size: 14pt;
    line-height: 1.55;
  }

  li {
    margin-left: 20px;
  }

  pre, code {
    font-size: 11pt;
  }

  a {
    text-decoration: none;
  }
`

const Header = styled.header`
  margin: 3vw auto;
  display: flex;
  justify-content: center;
`;

const Main = styled.main`
  max-width: 1000px;
  margin: auto;
`;

const Monic = styled.span`
  font-weight: 400;
  letter-spacing: 2px;
`;

const H1 = styled.h1`
  font-family: Nunino, sans-serif;
  font-weight: 300;
  margin-top: 0;
  margin-bottom: 100px;
`;

require("./theme.css");

export default class Template extends React.Component {
  render() {
    const { children } = this.props

    return (
      <div>
        <Header>
          <H1>
            <Link
              style={{
                boxShadow: 'none',
                textDecoration: 'none',
                color: 'inherit',
              }}
              to="/"
            >
              <Monic>MONIC</Monic>
              {' '}
              Blog
            </Link>
          </H1>
        </Header>
        <Main>{children()}</Main>
      </div>
    )
  }
}
